
namespace InsertSort

def insert (t : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [t]
  | x :: xs => if t <= x
               then t :: x ::xs
               else x :: insert t xs

def sort : List Nat -> List Nat
  | [] => []
  | x :: xs => insert x (sort xs)

inductive Sorted : List Nat → Prop where
  | nil   : Sorted []
  | single (x : Nat) : Sorted [x]
  | cons   (x y : Nat) (l : List Nat) :
      x ≤ y → Sorted (y :: l) → Sorted (x :: y :: l)

def is_a_sorting_algorithm (f : List Nat → List Nat) : Prop :=
  ∀ l, List.Perm (f l) l ∧ Sorted (f l)

theorem insert_sorted (t: Nat) (l : List Nat) (hl: Sorted l) : Sorted (insert t l) := by
  induction l generalizing t with
  | nil => exact Sorted.single t
  | cons x xs ih =>
      cases hl with
      |single x =>
        rw [insert]
        by_cases htx : t ≤ x
        .
          rw [if_pos htx]; exact Sorted.cons t x [] htx (Sorted.single x)
        .
          rw [if_neg htx]; exact Sorted.cons x t [] (Nat.le_of_not_le htx) (Sorted.single t)
      |cons _ y tl hxy htl =>
         rw [insert]
         by_cases htx : t ≤ x
         . -- t ≤ x
           rw [if_pos htx]; apply Sorted.cons t x (y :: tl) htx (Sorted.cons x y tl hxy htl)
         . -- t > x
           rw [if_neg htx, insert]
           have h4 := ih t htl
           by_cases hty : t ≤ y
           . -- t ≤ y
             rw [if_pos hty]
             apply Sorted.cons x t (y :: tl) (Nat.le_of_not_le htx) _
             apply Sorted.cons t y tl hty htl
           . -- t > y
             rw [if_neg hty]
             simp [insert, if_neg hty] at h4
             apply Sorted.cons x y (insert t tl) hxy h4

theorem sort_sorted (l : List Nat) : Sorted (sort l) := by
  induction l with
  | nil => exact Sorted.nil
  | cons x xs ih => exact insert_sorted x (sort xs) ih

theorem insert_perm (t : Nat) (l : List Nat) : List.Perm (t :: l) (insert t l) := by
  induction l with
  | nil => unfold insert; simp
  | cons x xs ih =>
      unfold insert;
      by_cases htx : t ≤ x
      .
        rw [if_pos htx]
      .
        rw [if_neg htx]
        apply List.Perm.trans (l₂ := x :: t :: xs )
          (List.Perm.swap x t xs)
          (List.Perm.cons x ih)

theorem sort_perm (l : List Nat) : List.Perm l (sort l) := by
  induction l with
  | nil => unfold sort; simp
  | cons x xs ih =>
      unfold sort;
      apply List.Perm.trans (l₂ := x :: (sort xs)) (List.Perm.cons x ih) (insert_perm _ _)

theorem insertion_sort_correct : is_a_sorting_algorithm sort := by
  intro lst
  apply And.intro (sort_perm lst).symm (sort_sorted lst)


end InsertSort
