
import Mathlib.Tactic

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


theorem insert_sorted (t : Nat) (l : List Nat) (hl : Sorted l) : Sorted (insert t l) := by
  induction hl generalizing t with
  | nil => unfold insert; exact Sorted.single t
  | single x =>
      unfold insert; split_ifs with htx <;> apply Sorted.cons _ _ [] (by linarith) (Sorted.single _)
  | cons x0 x1 lst h_x0_x1 h_x1_lst ih  =>
      unfold insert; split_ifs with htx
      · -- t ≤ x0
        apply Sorted.cons t x0 (x1 :: lst) htx _
        have h2 := ih x0; unfold insert at h2; rw [if_pos h_x0_x1] at h2
        exact h2
      · -- t > x0
        have h3 := ih t; unfold insert at h3 ⊢
        split_ifs at h3 ⊢ with htx1 <;> apply Sorted.cons x0 _ _  (by linarith) h3


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
      · rw [if_pos htx]
      · rw [if_neg htx]
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


def Sorted' (lst : List Nat) : Prop := ∀ (i j iv jv: Nat),
  i < j →
  lst[i]? = some iv →
  lst[j]? = some jv →
  iv ≤ jv



theorem sorted_sorted' : ∀ lst, Sorted lst → Sorted' lst := by
  intro lst h_lst;
  induction h_lst with
  | nil => unfold Sorted'; intro i j iv jv hij h_iv h_jv; cases i <;> simp at h_iv
  | single x =>
      unfold Sorted'; intro i j iv jv hij h_iv h_jv;
      match i, j with
      | 0, 0 => simp at h_iv h_jv; linarith
      | i+1, _ => simp at h_iv
      | _, j+1 => simp at h_jv
  | cons x y lst h_xy h_yl ih =>
      unfold Sorted'; intro i j iv jv hij h_iv h_jv;
      match i, j with
      | i, 0 => simp at hij
      | 0, 1 => simp at h_iv h_jv; linarith
      | i+1, 1 => simp at hij
      | 0, j+2 =>
         simp at h_iv h_jv;
         have h3 := ih 0 (j+1) y jv (by linarith) (by simp) (by tauto)
         linarith
      | i+1, j+1 => simp at h_iv h_jv; apply ih i j iv jv (by linarith) h_iv h_jv

-- ---------------------------------

def List_fa (lst : List Nat) (f : Nat -> Prop) : Prop :=
  ∀ (i iv: Nat), lst[i]? = some iv -> f iv

theorem list_fa_cdr : ∀ (x : Nat) (xs : List Nat) (f: Nat -> Prop),
  List_fa (x :: xs) f -> List_fa xs f := by
  intro x xs f h_f_x_xs i iv h_iv
  apply h_f_x_xs (i+1) iv (by tauto)


theorem list_fa_nil : ∀ (f : Nat -> Prop), List_fa [] f := by
  intro f i iv h_iv
  cases i <;> simp at h_iv

theorem list_fa_cons : ∀ (f : Nat -> Prop) (x: Nat) (xs: List Nat),
  f x -> List_fa xs f -> List_fa (x :: xs) f := by
  intro f x xs h_fx h_fxs i iv h_iv
  match i with
  | 0 => simp at h_iv; rw [<- h_iv]; assumption
  | i+1 => simp at h_iv; exact h_fxs i iv h_iv


theorem list_fa_perm : ∀ (l1 l2 : List Nat) (f: Nat -> Prop),
  List.Perm l1 l2 -> List_fa l1 f -> List_fa l2 f := by
  intro l1 l2 f h_l1_l2
  induction h_l1_l2 with
  | nil => tauto
  | @cons x l1 l2 h_l1_l2 ih_l1_l2 =>
      intro h i iv h_iv
      cases i with
      | zero => simp at h_iv ; have h3 := h 0 iv; simp at h3; apply h3 h_iv;
      | succ i => simp at h_iv; apply ih_l1_l2 (list_fa_cdr _ _ _ h) i iv h_iv
  | @swap x y lst =>
      intro h i iv h_iv;
      match i with
      | 0 => simp at h_iv; have h3 := h 1 iv; simp at h3; apply h3 h_iv
      | 1 => simp at h_iv; have h3 := h 0 iv; simp at h3; apply h3 h_iv
      | i+2 => simp at h_iv; have h3 := h (i+2) iv; simp at h3; apply h3 h_iv
  | @trans l1 l2 l3 h_l1_l2 h_l2_l3 ih_l1_l2 ih_l2_l3 =>
      intro h; apply ih_l2_l3 (ih_l1_l2 h)

theorem sorted'_nil : Sorted' [] := by
  unfold Sorted'; intro i j iv jv h_ij h_iv h_jv
  match i, j with
  | i, 0 => simp at h_ij
  | i, j+1 => simp at h_jv

theorem sorted'_single : ∀ x, Sorted' [x] := by
  unfold Sorted'; intro x i j iv jv h_ij h_iv h_jv
  match i, j with
  | i, 0 => simp at h_ij
  | i, j+1 => simp at h_jv

theorem sorted'_cdr : ∀ {x xs}, Sorted' (x :: xs) → Sorted' xs := by
  intro x xs h_x_xs i j iv jv h_ij h_iv h_jv
  apply h_x_xs (i+1) (j+1) iv jv (by linarith) (by tauto) (by tauto)

theorem sorted'_cons :
  ∀ {x xs}, Sorted' xs → List_fa xs (fun t => x ≤ t) -> Sorted' (x :: xs) := by
  intro x xs h_xs h_x_xs i j iv jv h_ij h_iv h_jv
  match i, j with
  | i, 0 => simp at h_ij
  | 0, j+1 => simp at h_iv h_jv; rw [<- h_iv]; apply h_x_xs j jv h_jv
  | i+1, j+1 =>
      simp at h_iv h_jv;
      exact h_xs i j iv jv (by linarith) (h_iv) (h_jv)

theorem sorted'_cons_cons :
  ∀ {x0 x1 xs}, x0 ≤ x1 -> Sorted' (x1 :: xs) -> Sorted' (x0 :: x1 :: xs) := by
  intro x0 x1 xs h_x0_x1 h_x1_xs
  apply sorted'_cons h_x1_xs _
  intro i iv h_iv
  match i with
  | 0 => simp at h_iv; linarith
  | i+1 =>
      simp at h_iv;
      have h2 := h_x1_xs 0 (i+1) x1 iv (by linarith) (by tauto) (by tauto)
      linarith

theorem sorted'_x0_x1_xs_sorted'_x0_xs :
  ∀ {x0 x1 xs}, Sorted' (x0 :: x1 :: xs) → Sorted' (x0 :: xs) := by
  intro x0 x1 xs h_x0_x1_xs
  have h_sorted_xs := h_x0_x1_xs |> sorted'_cdr |> sorted'_cdr
  apply sorted'_cons h_sorted_xs _; intro i iv h_iv;
  apply h_x0_x1_xs 0 (i+2) x0 iv (by linarith) (by tauto) (by tauto)

theorem sorted'_sorted : ∀ lst, Sorted' lst → Sorted lst := by
  intro lst h_lst
  induction lst with
  | nil => tauto
  | cons x xs ih =>
      cases xs with
      | nil => exact Sorted.single x
      | cons x1 xs =>
          have h_x_x1 : x ≤ x1 := h_lst 0 1 x x1 (by linarith) (by tauto) (by tauto)
          apply Sorted.cons x x1 xs h_x_x1 (ih (sorted'_cdr h_lst))


def elem_in_list (t : Nat) (lst : List Nat) : Prop := ∃ (i: Nat), lst[i]? = some t




theorem elem_in_xs_elem_in_x_xs : ∀ {t x : Nat} {xs: List Nat},
  elem_in_list t xs -> elem_in_list t (x :: xs) := by
  intro t x xs ⟨i, hi⟩; exists (i+1)

theorem elem_in_x_xs : ∀ {t x : Nat} {xs: List Nat},
  elem_in_list t (x :: xs) -> t = x ∨ elem_in_list t xs := by
  intro t x xs ⟨i, hi⟩
  match i with
  | 0 => simp at hi; rw[hi]; tauto
  | i+1 => simp at hi; right; exists i

theorem elem_in_perm : ∀ {t : Nat} {l1 l2 : List Nat},
  List.Perm l1 l2 -> elem_in_list t l1 -> elem_in_list t l2 := by
  intro t l1 l2 h_l1_l2
  induction h_l1_l2 generalizing t with
  | nil => tauto
  | @trans l1 l2 l3 h_l12 h_l23 ih_l12 ih_l23 => intro h; exact ih_l23 (ih_l12 h)
  | @swap  x y lst =>
      intro ⟨i, hi⟩
      match i with
      | 0 => exists 1
      | 1 => exists 0
      | j+2 => exists (j+2)
  | @cons x l1 l2 h_l1_l2 ih =>
      intro h_t_x_l1
      match (elem_in_x_xs h_t_x_l1) with
      | Or.inl left => exists 0; simp; tauto;
      | Or.inr right =>
          apply elem_in_xs_elem_in_x_xs (ih right);

theorem nth_error_insert : ∀ (l: List Nat) (a i iv: Nat),
    (insert a l)[i]? = some iv →
    a = iv ∨ ∃ (i': Nat), l[i']? = some iv := by
    intro lst a i iv h1
    rw [eq_comm, <- elem_in_list]
    apply elem_in_x_xs
    have h1 : elem_in_list iv (insert a lst) := by exists i
    exact elem_in_perm (t := iv) (l1 := insert a lst) (l2 := a :: lst) (insert_perm a lst).symm h1

theorem insert_sorted' : ∀ a lst, Sorted' lst → Sorted' (insert a lst) := by
  intro a lst h_lst
  induction lst generalizing a with
  | nil => unfold insert; apply sorted'_single
  | cons x xs ih =>
      unfold insert
      split_ifs with h_ax
      · apply sorted'_cons_cons h_ax h_lst
      · have h7 := ih a (sorted'_cdr h_lst)
        have h8 := sorted'_cons (x := x) (xs := insert a xs) h7
        apply h8
        apply list_fa_perm _ _ (fun t => x ≤ t) (insert_perm a xs)
        intro i iv h_iv
        match i with
        | 0 => simp at h_iv; linarith
        | i+1 =>
            simp at h_iv;
            apply h_lst 0 (i+1) x iv (by linarith) (by tauto) h_iv

theorem sort_sorted': ∀ l, Sorted' (sort l) := by
  intro l
  induction l with
  | nil => unfold sort; exact sorted'_nil
  | cons x xs ih =>
      unfold sort; apply insert_sorted' x (sort xs) ih

end InsertSort
