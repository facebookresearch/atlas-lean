/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.LeeYangPolynomial
import Mathlib.Algebra.Polynomial.Reverse

open scoped BigOperators
open Finset Polynomial

namespace StatMech.FrontierC

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def leeYangFlip (s : ConfigSpace V) : ConfigSpace V := fun x => !(s x)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem leeYangFlip_apply (s : ConfigSpace V) (x : V) :
    leeYangFlip s x = !(s x) := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem leeYangFlip_involutive (s : ConfigSpace V) :
    leeYangFlip (leeYangFlip s) = s := by
  funext x
  simp [leeYangFlip]


def leeYangFlipEquiv : ConfigSpace V ≃ ConfigSpace V where
  toFun := leeYangFlip
  invFun := leeYangFlip
  left_inv := leeYangFlip_involutive
  right_inv := leeYangFlip_involutive

omit [Fintype V] [DecidableEq V] in
@[simp] theorem leeYangFlipEquiv_apply (s : ConfigSpace V) :
    leeYangFlipEquiv s = leeYangFlip s := rfl

omit [DecidableEq V] in
theorem minusSpinCount_flip (s : ConfigSpace V) :
    minusSpinCount (leeYangFlip s) = Fintype.card V - minusSpinCount s := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun x : V => s x = false)
  have hnot : (Finset.univ.filter fun x : V => ¬s x = false) =
      Finset.univ.filter fun x : V => s x = true := by
    ext x
    cases hx : s x <;> simp [hx]
  rw [hnot, Finset.card_univ] at hpartition
  unfold minusSpinCount leeYangFlip
  have hflip : (Finset.univ.filter fun x : V => Bool.not (s x) = false) =
      Finset.univ.filter fun x : V => s x = true := by
    ext x
    cases hx : s x <;> simp [hx]
  rw [hflip]
  omega

omit [Fintype V] [DecidableEq V] in
theorem bond_leeYangFlip (s : ConfigSpace V) (e : Sym2 V) :
    bond (leeYangFlip s) e = bond s e := by
  induction e with
  | h a b =>
      simp only [bond_mk]
      unfold spin leeYangFlip
      cases s a <;> cases s b <;> simp

omit [DecidableEq V] in
theorem zeroFieldInteractionWeight_flip (beta : ℝ) (s : ConfigSpace V) :
    zeroFieldInteractionWeight G beta (leeYangFlip s) =
      zeroFieldInteractionWeight G beta s := by
  unfold zeroFieldInteractionWeight
  congr 2
  exact Finset.sum_congr rfl (fun e _ => bond_leeYangFlip s e)

private theorem coeff_leeYangPolynomial (beta : ℝ) (k : ℕ) :
    (leeYangPolynomial G beta).coeff k =
      ∑ s : ConfigSpace V,
        if k = minusSpinCount s then zeroFieldInteractionWeight G beta s else 0 := by
  simp [leeYangPolynomial]



theorem leeYangPolynomial_coeff_symm (beta : ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    (leeYangPolynomial G beta).coeff k =
      (leeYangPolynomial G beta).coeff (Fintype.card V - k) := by
  rw [coeff_leeYangPolynomial, coeff_leeYangPolynomial]
  let f : ConfigSpace V → ℝ := fun s =>
    if k = minusSpinCount s then zeroFieldInteractionWeight G beta s else 0
  calc
    (∑ s : ConfigSpace V,
        if k = minusSpinCount s then zeroFieldInteractionWeight G beta s else 0) =
        ∑ s : ConfigSpace V, f (leeYangFlipEquiv s) := by
          simpa only [f] using
            (Equiv.sum_comp leeYangFlipEquiv f).symm
    _ = ∑ s : ConfigSpace V,
        if Fintype.card V - k = minusSpinCount s then
          zeroFieldInteractionWeight G beta s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [f, leeYangFlipEquiv_apply, minusSpinCount_flip,
        zeroFieldInteractionWeight_flip]
      have hcount : minusSpinCount s ≤ Fintype.card V := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      by_cases heq : k = Fintype.card V - minusSpinCount s
      · rw [if_pos heq]
        rw [if_pos]
        omega
      · rw [if_neg heq]
        rw [if_neg]
        omega

lemma leeYangPolynomial_natDegree_le (beta : ℝ) :
    (leeYangPolynomial G beta).natDegree ≤ Fintype.card V := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_leeYangPolynomial]
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg]
  have hcount : minusSpinCount s ≤ Fintype.card V :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

lemma leeYangPolynomial_coeff_card_pos (beta : ℝ) :
    0 < (leeYangPolynomial G beta).coeff (Fintype.card V) := by
  rw [coeff_leeYangPolynomial]
  let sMinus : ConfigSpace V := fun _ => false
  have hminus : minusSpinCount sMinus = Fintype.card V := by
    simp [sMinus, minusSpinCount]
  have hterm : 0 <
      (if Fintype.card V = minusSpinCount sMinus then
        zeroFieldInteractionWeight G beta sMinus else 0) := by
    rw [if_pos hminus.symm]
    exact Real.exp_pos _
  have hnonneg : ∀ s ∈ (Finset.univ : Finset (ConfigSpace V)),
      0 ≤ (if Fintype.card V = minusSpinCount s then
        zeroFieldInteractionWeight G beta s else 0) := by
    intro s _
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  exact hterm.trans_le (Finset.single_le_sum hnonneg (Finset.mem_univ sMinus))



theorem leeYangPolynomial_natDegree (beta : ℝ) :
    (leeYangPolynomial G beta).natDegree = Fintype.card V :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (leeYangPolynomial_natDegree_le G beta)
    (ne_of_gt (leeYangPolynomial_coeff_card_pos G beta))


theorem leeYangPolynomial_reverse (beta : ℝ) :
    (leeYangPolynomial G beta).reverse = leeYangPolynomial G beta := by
  ext k
  rw [Polynomial.coeff_reverse, leeYangPolynomial_natDegree]
  by_cases hk : k ≤ Fintype.card V
  · rw [Polynomial.revAt_le hk]
    exact (leeYangPolynomial_coeff_symm G beta hk).symm
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hk)]


theorem leeYangComplexPolynomial_coeff_symm (beta : ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    (leeYangComplexPolynomial G beta).coeff k =
      (leeYangComplexPolynomial G beta).coeff (Fintype.card V - k) := by
  simp only [leeYangComplexPolynomial, Polynomial.coeff_map]
  rw [leeYangPolynomial_coeff_symm G beta hk]


theorem leeYangComplexPolynomial_natDegree (beta : ℝ) :
    (leeYangComplexPolynomial G beta).natDegree = Fintype.card V := by
  unfold leeYangComplexPolynomial
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
  exact leeYangPolynomial_natDegree G beta


theorem leeYangComplexPolynomial_reverse (beta : ℝ) :
    (leeYangComplexPolynomial G beta).reverse =
      leeYangComplexPolynomial G beta := by
  ext k
  rw [Polynomial.coeff_reverse, leeYangComplexPolynomial_natDegree]
  by_cases hk : k ≤ Fintype.card V
  · rw [Polynomial.revAt_le hk]
    exact (leeYangComplexPolynomial_coeff_symm G beta hk).symm
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hk)]


theorem leeYangPolynomial_coeff_zero_pos (beta : ℝ) :
    0 < (leeYangPolynomial G beta).coeff 0 := by
  rw [leeYangPolynomial_coeff_symm G beta (Nat.zero_le _), Nat.sub_zero]
  exact leeYangPolynomial_coeff_card_pos G beta


theorem leeYangComplexPolynomial_eval_zero_ne_zero (beta : ℝ) :
    (leeYangComplexPolynomial G beta).eval 0 ≠ 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp only [leeYangComplexPolynomial, Polynomial.coeff_map]
  exact (map_ne_zero (algebraMap ℝ ℂ)).2
    (ne_of_gt (leeYangPolynomial_coeff_zero_pos G beta))




theorem leeYangComplexPolynomial_eval_inv_eq_zero_iff (beta : ℝ) {z : ℂ}
    (hz : z ≠ 0) :
    (leeYangComplexPolynomial G beta).eval z⁻¹ = 0 ↔
      (leeYangComplexPolynomial G beta).eval z = 0 := by
  letI : Invertible z := invertibleOfNonzero hz
  have h := Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id ℂ) z
    (leeYangComplexPolynomial G beta)
  rw [leeYangComplexPolynomial_reverse G beta] at h
  simpa only [Polynomial.eval₂_id, invOf_eq_inv] using h




theorem leeYangComplexPolynomial_eval_inv_eq_zero_iff' (beta : ℝ) (z : ℂ) :
    (leeYangComplexPolynomial G beta).eval z⁻¹ = 0 ↔
      (leeYangComplexPolynomial G beta).eval z = 0 := by
  by_cases hz : z = 0
  · subst z
    simp only [inv_zero]
  · exact leeYangComplexPolynomial_eval_inv_eq_zero_iff G beta hz


theorem leeYangComplexPolynomial_root_ne_zero (beta : ℝ) {z : ℂ}
    (hz : (leeYangComplexPolynomial G beta).eval z = 0) : z ≠ 0 := by
  intro hzero
  subst z
  exact leeYangComplexPolynomial_eval_zero_ne_zero G beta hz


theorem leeYangComplexPolynomial_isRoot_inv_iff (beta : ℝ) (z : ℂ) :
    (leeYangComplexPolynomial G beta).IsRoot z⁻¹ ↔
      (leeYangComplexPolynomial G beta).IsRoot z := by
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def]
  exact leeYangComplexPolynomial_eval_inv_eq_zero_iff' G beta z


theorem leeYangComplexPolynomial_isRoot_ne_zero (beta : ℝ) {z : ℂ}
    (hz : (leeYangComplexPolynomial G beta).IsRoot z) : z ≠ 0 :=
  leeYangComplexPolynomial_root_ne_zero G beta (Polynomial.IsRoot.def.mp hz)

end StatMech.FrontierC
