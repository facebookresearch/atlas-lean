/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianConePolarization
import Code.FrontierA.LeeYangAsano










open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



def leeYangWeightedDiagonal (a : V -> Real) (z : Complex) :
    LeeYangVar G -> Complex
  | Sum.inl v => Complex.exp (-2 * (a v : Complex) * z)
  | Sum.inr _ => 0

theorem leeYangWeightedDiagonal_norm_lt
    (a : V -> Real) (ha : forall v, 0 < a v)
    {z : Complex} (hz : 0 < z.re) :
    forall k, ‖leeYangWeightedDiagonal G a z k‖ < 1 := by
  intro k
  rcases k with v | ⟨v, e⟩
  · unfold leeYangWeightedDiagonal
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    norm_num [Complex.mul_re]
    nlinarith [ha v]
  · simp [leeYangWeightedDiagonal]



theorem leeYangContractedProduct_weighted_ne_zero
    {beta : Real} (hbeta : 0 <= beta)
    (a : V -> Real) (ha : forall v, 0 < a v)
    {z : Complex} (hz : 0 < z.re) :
    leeYangContractedProduct G beta (leeYangWeightedDiagonal G a z) ≠ 0 := by
  apply leeYangContractedProduct_stable G hbeta
  exact leeYangWeightedDiagonal_norm_lt G a ha hz




def finiteIsingWeightedFieldPartition
    (beta : Real) (a : V -> Real) (z : Complex) : Complex :=
  ∑ s : ConfigSpace V, (zeroFieldInteractionWeight G beta s : Complex) *
    Complex.exp (z * ∑ v : V, (a v : Complex) * spin s v)

theorem leeYangMonomial_anchorSupport_weighted
    (sigma : V -> Bool) (a : V -> Real) (z : Complex) :
    leeYangMonomial (leeYangAnchorSupport G sigma)
        (leeYangWeightedDiagonal G a z) =
      ∏ v : V, if sigma v = true then
        Complex.exp (-2 * (a v : Complex) * z) else 1 := by
  unfold leeYangMonomial leeYangAnchorSupport leeYangWeightedDiagonal
  rw [Finset.prod_filter]
  simp only [Fintype.prod_sum_type, if_false]
  simp

theorem exp_weightedSpin_eq_total_mul_monomial_flip
    (s : ConfigSpace V) (a : V -> Real) (z : Complex) :
    Complex.exp (z * ∑ v : V, (a v : Complex)) *
        leeYangMonomial (leeYangAnchorSupport G (leeYangFlip s))
          (leeYangWeightedDiagonal G a z) =
      Complex.exp (z * ∑ v : V, (a v : Complex) * spin s v) := by
  rw [leeYangMonomial_anchorSupport_weighted]
  have hprod :
      (∏ v : V, if leeYangFlip s v = true then
          Complex.exp (-2 * (a v : Complex) * z) else 1) =
        Complex.exp (∑ v : V, if leeYangFlip s v = true then
          -2 * (a v : Complex) * z else 0) := by
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro v _
    cases hv : s v <;> simp [leeYangFlip, hv]
  rw [hprod, ← Complex.exp_add]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  unfold leeYangFlip spin
  cases h : s v <;> simp [h]
  ring



theorem leeYangContractedProduct_weighted_eq_partition
    (beta : Real) (a : V -> Real) (z : Complex) :
    (Real.exp (beta * G.edgeFinset.card) : Complex) *
        Complex.exp (z * ∑ v : V, (a v : Complex)) *
        leeYangContractedProduct G beta (leeYangWeightedDiagonal G a z) =
      finiteIsingWeightedFieldPartition G beta a z := by
  rw [leeYangContractedProduct_eq_sum_sigma, Finset.mul_sum,
    Finset.mul_sum]
  let F : ConfigSpace V -> Complex := fun sigma =>
    (Real.exp (beta * G.edgeFinset.card) : Complex) *
      Complex.exp (∑ v : V, z * (a v : Complex)) *
      (leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) *
        leeYangMonomial (leeYangAnchorSupport G sigma)
          (leeYangWeightedDiagonal G a z))
  unfold finiteIsingWeightedFieldPartition
  change (∑ sigma : ConfigSpace V, F sigma) = _
  rw [show (∑ sigma : ConfigSpace V, F sigma) =
      ∑ s : ConfigSpace V, F (leeYangFlipEquiv s) by
        simpa using (Equiv.sum_comp leeYangFlipEquiv F).symm]
  apply Finset.sum_congr rfl
  intro s _
  have hweight :
      (Real.exp (beta * G.edgeFinset.card) : Complex) *
          leeYangChoiceWeight G beta
            (leeYangFlip s, leeYangTauOf G (leeYangFlip s)) =
        (zeroFieldInteractionWeight G beta s : Complex) := by
    rw [leeYangChoiceWeight_eq_ofReal]
    rw [← Complex.ofReal_mul]
    rw [exp_card_mul_leeYangRealChoiceWeight]
    rw [zeroFieldInteractionWeight_flip]
  have hfield := exp_weightedSpin_eq_total_mul_monomial_flip G s a z
  rw [Finset.mul_sum] at hfield
  simp only [F, leeYangFlipEquiv_apply]
  calc
    (Real.exp (beta * G.edgeFinset.card) : Complex) *
          Complex.exp (∑ v : V, z * (a v : Complex)) *
          (leeYangChoiceWeight G beta
              (leeYangFlip s, leeYangTauOf G (leeYangFlip s)) *
            leeYangMonomial (leeYangAnchorSupport G (leeYangFlip s))
              (leeYangWeightedDiagonal G a z)) =
        ((Real.exp (beta * G.edgeFinset.card) : Complex) *
            leeYangChoiceWeight G beta
              (leeYangFlip s, leeYangTauOf G (leeYangFlip s))) *
          (Complex.exp (∑ v : V, z * (a v : Complex)) *
            leeYangMonomial (leeYangAnchorSupport G (leeYangFlip s))
              (leeYangWeightedDiagonal G a z)) := by ring
    _ = (zeroFieldInteractionWeight G beta s : Complex) *
          Complex.exp (z * ∑ v : V, (a v : Complex) * spin s v) := by
      rw [hweight, hfield]



theorem finiteIsingWeightedFieldPartition_ne_zero
    {beta : Real} (hbeta : 0 <= beta)
    (a : V -> Real) (ha : forall v, 0 < a v)
    {z : Complex} (hz : 0 < z.re) :
    finiteIsingWeightedFieldPartition G beta a z ≠ 0 := by
  have hcontracted :=
    leeYangContractedProduct_weighted_ne_zero G hbeta a ha hz
  intro hzero
  have hproduct :
      (Real.exp (beta * G.edgeFinset.card) : Complex) *
          Complex.exp (z * ∑ v : V, (a v : Complex)) *
          leeYangContractedProduct G beta (leeYangWeightedDiagonal G a z) = 0 := by
    rw [leeYangContractedProduct_weighted_eq_partition, hzero]
  rcases mul_eq_zero.mp hproduct with hleft | hcontractedZero
  · rcases mul_eq_zero.mp hleft with hbetaZero | hexpZero
    · have hbetaExp :
          (Real.exp (beta * G.edgeFinset.card) : Complex) ≠ 0 := by
        exact_mod_cast Real.exp_ne_zero (beta * G.edgeFinset.card)
      exact hbetaExp hbetaZero
    · exact Complex.exp_ne_zero _ hexpZero
  · exact hcontracted hcontractedZero

theorem finiteIsingWeightedFieldPartition_neg
    (beta : Real) (a : V -> Real) (z : Complex) :
    finiteIsingWeightedFieldPartition G beta a (-z) =
      finiteIsingWeightedFieldPartition G beta a z := by
  unfold finiteIsingWeightedFieldPartition
  let F : ConfigSpace V -> Complex := fun s =>
    (zeroFieldInteractionWeight G beta s : Complex) *
      Complex.exp (-z * ∑ v : V, (a v : Complex) * spin s v)
  change (∑ s : ConfigSpace V, F s) = _
  rw [show (∑ s : ConfigSpace V, F s) =
      ∑ s : ConfigSpace V, F (leeYangFlipEquiv s) by
        simpa using (Equiv.sum_comp leeYangFlipEquiv F).symm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [F, leeYangFlipEquiv_apply, zeroFieldInteractionWeight_flip]
  congr 2
  have hspin :
      (∑ v : V, (a v : Complex) * spin (leeYangFlip s) v) =
        -(∑ v : V, (a v : Complex) * spin s v) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    unfold leeYangFlip spin
    cases h : s v <;> simp [h]
  rw [hspin]
  ring




theorem finiteIsingWeightedFieldPartition_ne_zero_of_re_ne_zero
    {beta : Real} (hbeta : 0 <= beta)
    (a : V -> Real) (ha : forall v, 0 < a v)
    {z : Complex} (hz : z.re ≠ 0) :
    finiteIsingWeightedFieldPartition G beta a z ≠ 0 := by
  rcases lt_or_gt_of_ne hz.symm with hzpos | hzneg
  · exact finiteIsingWeightedFieldPartition_ne_zero G hbeta a ha hzpos
  · have hnegRe : 0 < (-z).re := by simpa using neg_pos.mpr hzneg
    have hnonzero := finiteIsingWeightedFieldPartition_ne_zero
      G hbeta a ha hnegRe
    rwa [finiteIsingWeightedFieldPartition_neg] at hnonzero

end

end StatMech.FrontierA
