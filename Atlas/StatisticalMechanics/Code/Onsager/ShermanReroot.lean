/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanLemma4
import Code.Onsager.ShermanSplit










namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {n : ℕ} [NeZero n]


def ons_rotate (k : Fin n) (v : Fin n → E) : Fin n → E :=
  fun j => v (j + k)

@[simp] theorem ons_rotate_apply (k j : Fin n) (v : Fin n → E) :
    ons_rotate k v j = v (j + k) := rfl

@[simp] theorem ons_rotate_zero (k : Fin n) (v : Fin n → E) :
    ons_rotate k v 0 = v k := by
  simp [ons_rotate]


def ons_rotateEquiv (k : Fin n) : (Fin n → E) ≃ (Fin n → E) where
  toFun := ons_rotate k
  invFun := ons_rotate (-k)
  left_inv v := by
    funext j
    simp [ons_rotate, add_assoc]
  right_inv v := by
    funext j
    simp [ons_rotate, add_assoc]

theorem ons_rotate_eq_iterate (k : Fin n) (v : Fin n → E) :
    ons_rotate k v = ons_cyclicShift^[k.val] v := by
  rw [ons_cyclicShift_iterate_apply]
  funext j
  unfold ons_rotate
  congr 1
  apply Fin.ext
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt k.isLt]


theorem ons_loopWeight_rotate (Lambda : Matrix E E ℂ) (k : Fin n) (v : Fin n → E) :
    ons_loopWeight Lambda (ons_rotate k v) = ons_loopWeight Lambda v := by
  rw [ons_rotate_eq_iterate]
  exact ons_iterate_inv (ons_loopWeight_cyclicShift Lambda) v k.val


def ons_visitCount (e : E) (v : Fin n → E) : ℕ :=
  Fintype.card {k : Fin n // v k = e}

theorem ons_visitCount_eq_card_filter (e : E) (v : Fin n → E) :
    ons_visitCount e v = (Finset.univ.filter fun k : Fin n => v k = e).card := by
  unfold ons_visitCount
  rw [← Finset.card_subtype]
  simp

theorem ons_visitCount_pos_iff (e : E) (v : Fin n → E) :
    0 < ons_visitCount e v ↔ ∃ k, v k = e := by
  rw [ons_visitCount_eq_card_filter, Finset.card_pos]
  rw [Finset.filter_nonempty_iff]
  simp


theorem ons_visitCount_rotate (e : E) (k : Fin n) (v : Fin n → E) :
    ons_visitCount e (ons_rotate k v) = ons_visitCount e v := by
  unfold ons_visitCount
  apply Fintype.card_congr
  exact
    { toFun := fun j => ⟨j.1 + k, j.2⟩
      invFun := fun j => ⟨j.1 - k, by
        simpa [ons_rotate, sub_add_cancel] using j.2⟩
      left_inv := fun j => by ext; simp
      right_inv := fun j => by ext; simp }


theorem ons_avoids_rotate (r : E) (k : Fin n) (v : Fin n → E) :
    (∀ j, ons_rotate k v j ≠ r) ↔ ∀ j, v j ≠ r := by
  constructor
  · intro h j
    have := h (j - k)
    simpa [ons_rotate, sub_add_cancel] using this
  · intro h j
    exact h (j + k)

private noncomputable def ons_rerootTerm (Lambda : Matrix E E ℂ) (e r : E)
    (v : Fin n → E) : ℂ :=
  if (∀ j, v j ≠ r) ∧ v 0 = e then
    ons_loopWeight Lambda v / (ons_visitCount e v : ℂ)
  else 0

private noncomputable def ons_markedTerm (Lambda : Matrix E E ℂ) (e r : E)
    (k : Fin n) (v : Fin n → E) : ℂ :=
  if (∀ j, v j ≠ r) ∧ v k = e then
    ons_loopWeight Lambda v / (ons_visitCount e v : ℂ)
  else 0

private theorem ons_markedTerm_eq_rerootTerm (Lambda : Matrix E E ℂ) (e r : E)
    (k : Fin n) (v : Fin n → E) :
    ons_markedTerm Lambda e r k v = ons_rerootTerm Lambda e r (ons_rotate k v) := by
  unfold ons_markedTerm ons_rerootTerm
  by_cases h : (∀ j, v j ≠ r) ∧ v k = e
  · rw [if_pos h]
    have hrot : (∀ j, ons_rotate k v j ≠ r) ∧ ons_rotate k v 0 = e :=
      ⟨(ons_avoids_rotate r k v).2 h.1, by simpa using h.2⟩
    rw [if_pos hrot, ons_loopWeight_rotate, ons_visitCount_rotate]
  · rw [if_neg h]
    have hrot : ¬ ((∀ j, ons_rotate k v j ≠ r) ∧ ons_rotate k v 0 = e) := by
      intro hr
      apply h
      exact ⟨(ons_avoids_rotate r k v).1 hr.1, by simpa using hr.2⟩
    rw [if_neg hrot]

private theorem ons_sum_markedTerm (Lambda : Matrix E E ℂ) (e r : E) (k : Fin n) :
    ∑ v : Fin n → E, ons_markedTerm Lambda e r k v =
      ∑ v : Fin n → E, ons_rerootTerm Lambda e r v := by
  simp_rw [ons_markedTerm_eq_rerootTerm]
  exact Equiv.sum_comp (ons_rotateEquiv k) (ons_rerootTerm Lambda e r)

private theorem ons_sum_marks_recovers_weight (Lambda : Matrix E E ℂ) (e r : E)
    (v : Fin n → E) :
    (∑ k : Fin n, ons_markedTerm Lambda e r k v) =
      if (∀ j, v j ≠ r) ∧ (∃ k, v k = e) then ons_loopWeight Lambda v else 0 := by
  unfold ons_markedTerm
  by_cases hav : ∀ j, v j ≠ r
  · have hterm : ∀ k : Fin n,
        (if (∀ j, v j ≠ r) ∧ v k = e then
            ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) else 0) =
          if v k = e then
            ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) else 0 := by
      intro k
      by_cases hk : v k = e <;> simp [hav, hk]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    by_cases hvis : ∃ k, v k = e
    · rw [if_pos ⟨hav, hvis⟩]
      have hcount : 0 < ons_visitCount e v := (ons_visitCount_pos_iff e v).2 hvis
      have hcountC : (ons_visitCount e v : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcount)
      have hsum : (∑ k : Fin n, if v k = e then (1 : ℂ) else 0) =
          (ons_visitCount e v : ℂ) := by
        rw [Finset.sum_boole, ons_visitCount_eq_card_filter]
      calc
        (∑ k : Fin n, if v k = e then
            ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) else 0) =
            (∑ k : Fin n, if v k = e then (1 : ℂ) else 0) *
              (ons_loopWeight Lambda v / (ons_visitCount e v : ℂ)) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro k _
                split_ifs <;> simp
        _ = ons_loopWeight Lambda v := by
          rw [hsum]
          field_simp [hcountC]
    · rw [if_neg (by exact fun h => hvis h.2)]
      push_neg at hvis
      simp [hvis]
  · have hcond : ¬ ((∀ j, v j ≠ r) ∧ ∃ k, v k = e) := by aesop
    rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    exact fun h => hav h.1







theorem ons_loopSum_div_length_eq_rerooted (Lambda : Matrix E E ℂ) (e r : E) :
    (∑ v ∈ Finset.univ.filter (fun v : Fin n → E =>
        (∃ k, v k = e) ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v) / (n : ℂ) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n → E =>
        v 0 = e ∧ ∀ j, v j ≠ r),
        ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hdouble :
      (∑ v : Fin n → E, ∑ k : Fin n, ons_markedTerm Lambda e r k v) =
        (n : ℂ) * ∑ v : Fin n → E, ons_rerootTerm Lambda e r v := by
    rw [Finset.sum_comm]
    simp_rw [ons_sum_markedTerm]
    simp
  have hleft :
      (∑ v : Fin n → E, ∑ k : Fin n, ons_markedTerm Lambda e r k v) =
        ∑ v ∈ Finset.univ.filter (fun v : Fin n → E =>
          (∃ k, v k = e) ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v := by
    simp_rw [ons_sum_marks_recovers_weight]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext v
      simp [and_comm]
    · simp
  have hright :
      (∑ v : Fin n → E, ons_rerootTerm Lambda e r v) =
        ∑ v ∈ Finset.univ.filter (fun v : Fin n → E =>
          v 0 = e ∧ ∀ j, v j ≠ r),
          ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
    unfold ons_rerootTerm
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext v
      simp [and_comm]
    · simp
  rw [hleft, hright] at hdouble
  apply (div_eq_iff hn).2
  simpa [mul_comm] using hdouble



theorem ons_firstReturnFactors_length (e : E) (v : Fin n → E) (hroot : v 0 = e) :
    (ons_firstReturnFactors e (List.ofFn v ++ [e])).length = ons_visitCount e v := by
  have hhead : (List.ofFn v ++ [e]).head? = some e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    subst n
    rw [List.ofFn_succ]
    simp [hroot]
  have hlast : (List.ofFn v ++ [e]).getLast? = some e := by simp
  have hspec := ons_firstReturnFactors_spec e (List.ofFn v ++ [e]) hhead hlast
  have hcount := ons_count_glue_firstReturn e
    (ons_firstReturnFactors e (List.ofFn v ++ [e])) hspec.2.1
  rw [hspec.2.2, List.count_append, ons_count_ofFn_eq_visitCount] at hcount
  simp only [List.count_singleton_self] at hcount
  unfold ons_visitCount
  omega

end StatMech.Onsager
