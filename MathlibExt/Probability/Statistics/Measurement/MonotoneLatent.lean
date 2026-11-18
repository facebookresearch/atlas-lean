/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.LatentMoments
public import Mathlib.Probability.Moments.Covariance

/-!
# Monotone latent curves and item covariance

When two item response curves are both monotone in a finite linearly
ordered latent state, the covariance of their response indicators
under the observed latent-mixture law is nonnegative.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory

private theorem finiteCovariance_nonneg_of_monotone {Z : Type*} [Fintype Z] [LinearOrder Z]
    (p X Y : Z → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hX0 : ∀ z, 0 ≤ X z) (hY0 : ∀ z, 0 ≤ Y z)
    (hXm : Monotone X) (hYm : Monotone Y) :
    0 ≤ MathlibExt.Probability.FiniteProbability.covariance p X Y := by
  simp only [MathlibExt.Probability.FiniteProbability.covariance,
    MathlibExt.Probability.FiniteProbability.expectation]
  set S := ∑ z, p z with hS
  set EX := ∑ z, p z * X z with hEX
  set EY := ∑ z, p z * Y z with hEY
  set EXY := ∑ z, p z * (X z * Y z) with hEXY
  have hS_nonneg : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg (fun z _ => hp z)
  have hEX_nonneg : 0 ≤ EX := by
    rw [hEX]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (hp z) (hX0 z))
  have hEY_nonneg : 0 ≤ EY := by
    rw [hEY]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (hp z) (hY0 z))
  have hCovEq : (∑ z, p z * ((X z - EX) * (Y z - EY)))
      = EXY - EX * EY * (2 - S) := by
    have hpt : ∀ z, p z * ((X z - EX) * (Y z - EY))
        = p z * (X z * Y z) - EY * (p z * X z) - EX * (p z * Y z) + EX * EY * p z := by
      intro z
      ring
    have hsum1 : (∑ z, p z * ((X z - EX) * (Y z - EY)))
        = ∑ z, (p z * (X z * Y z) - EY * (p z * X z) - EX * (p z * Y z) + EX * EY * p z) := by
      apply Finset.sum_congr rfl
      intro z _
      exact hpt z
    rw [hsum1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have hb : (∑ z, EY * (p z * X z)) = EY * EX := by
      rw [← Finset.mul_sum, ← hEX]
    have hc : (∑ z, EX * (p z * Y z)) = EX * EY := by
      rw [← Finset.mul_sum, ← hEY]
    have hd : (∑ z, EX * EY * p z) = EX * EY * S := by
      rw [← Finset.mul_sum, ← hS]
    rw [← hEXY, hb, hc, hd]
    ring
  have hterm_nonneg : ∀ a b, 0 ≤ p a * p b * ((X a - X b) * (Y a - Y b)) := by
    intro a b
    have hpp : 0 ≤ p a * p b := mul_nonneg (hp a) (hp b)
    have hdiff : 0 ≤ (X a - X b) * (Y a - Y b) := by
      rcases le_total a b with hab | hba
      · have hX : X a ≤ X b := hXm hab
        have hY : Y a ≤ Y b := hYm hab
        have heq : (X a - X b) * (Y a - Y b) = (X b - X a) * (Y b - Y a) := by ring
        rw [heq]
        exact mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)
      · have hX : X b ≤ X a := hXm hba
        have hY : Y b ≤ Y a := hYm hba
        exact mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)
    exact mul_nonneg hpp hdiff
  have hT1 : (∑ a, ∑ b, p a * p b * (X a * Y a)) = EXY * S := by
    have hinner : ∀ a, (∑ b, p a * p b * (X a * Y a)) = (p a * (X a * Y a)) * S := by
      intro a
      have hpt1 : ∀ b, p a * p b * (X a * Y a) = (p a * (X a * Y a)) * p b := fun b => by ring
      have h1 : (∑ b, p a * p b * (X a * Y a)) = ∑ b, (p a * (X a * Y a)) * p b := by
        apply Finset.sum_congr rfl
        intro b _
        exact hpt1 b
      rw [h1, ← Finset.mul_sum, ← hS]
    have h2 : (∑ a, ∑ b, p a * p b * (X a * Y a)) = ∑ a, (p a * (X a * Y a)) * S := by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner a
    rw [h2, ← Finset.sum_mul, ← hEXY]
  have hT4 : (∑ a, ∑ b, p a * p b * (X b * Y b)) = S * EXY := by
    have hinner : ∀ a, (∑ b, p a * p b * (X b * Y b)) = p a * EXY := by
      intro a
      have hpt4 : ∀ b, p a * p b * (X b * Y b) = p a * (p b * (X b * Y b)) := fun b => by ring
      have h1 : (∑ b, p a * p b * (X b * Y b)) = ∑ b, p a * (p b * (X b * Y b)) := by
        apply Finset.sum_congr rfl
        intro b _
        exact hpt4 b
      rw [h1, ← Finset.mul_sum, ← hEXY]
    have h2 : (∑ a, ∑ b, p a * p b * (X b * Y b)) = ∑ a, p a * EXY := by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner a
    rw [h2, ← Finset.sum_mul, ← hS]
  have hT2 : (∑ a, ∑ b, p a * p b * (X a * Y b)) = EX * EY := by
    have hinner : ∀ a, (∑ b, p a * p b * (X a * Y b)) = (p a * X a) * EY := by
      intro a
      have hpt2 : ∀ b, p a * p b * (X a * Y b) = (p a * X a) * (p b * Y b) := fun b => by ring
      have h1 : (∑ b, p a * p b * (X a * Y b)) = ∑ b, (p a * X a) * (p b * Y b) := by
        apply Finset.sum_congr rfl
        intro b _
        exact hpt2 b
      rw [h1, ← Finset.mul_sum, ← hEY]
    have h2 : (∑ a, ∑ b, p a * p b * (X a * Y b)) = ∑ a, (p a * X a) * EY := by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner a
    rw [h2, ← Finset.sum_mul, ← hEX]
  have hT3 : (∑ a, ∑ b, p a * p b * (X b * Y a)) = EY * EX := by
    have hinner : ∀ a, (∑ b, p a * p b * (X b * Y a)) = (p a * Y a) * EX := by
      intro a
      have hpt3 : ∀ b, p a * p b * (X b * Y a) = (p a * Y a) * (p b * X b) := fun b => by ring
      have h1 : (∑ b, p a * p b * (X b * Y a)) = ∑ b, (p a * Y a) * (p b * X b) := by
        apply Finset.sum_congr rfl
        intro b _
        exact hpt3 b
      rw [h1, ← Finset.mul_sum, ← hEX]
    have h2 : (∑ a, ∑ b, p a * p b * (X b * Y a)) = ∑ a, (p a * Y a) * EX := by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner a
    rw [h2, ← Finset.sum_mul, ← hEY]
  have hterm : ∀ a b, p a * p b * ((X a - X b) * (Y a - Y b))
      = p a * p b * (X a * Y a) - p a * p b * (X a * Y b)
        - p a * p b * (X b * Y a) + p a * p b * (X b * Y b) := by
    intro a b
    ring
  have hD_eq : (∑ a, ∑ b, p a * p b * ((X a - X b) * (Y a - Y b)))
      = 2 * (S * EXY - EX * EY) := by
    have hinner_eq : ∀ a, (∑ b, p a * p b * ((X a - X b) * (Y a - Y b)))
        = (∑ b, p a * p b * (X a * Y a)) - (∑ b, p a * p b * (X a * Y b))
          - (∑ b, p a * p b * (X b * Y a)) + (∑ b, p a * p b * (X b * Y b)) := by
      intro a
      have h1 : (∑ b, p a * p b * ((X a - X b) * (Y a - Y b)))
          = ∑ b, (p a * p b * (X a * Y a) - p a * p b * (X a * Y b)
            - p a * p b * (X b * Y a) + p a * p b * (X b * Y b)) := by
        apply Finset.sum_congr rfl
        intro b _
        exact hterm a b
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have h2 : (∑ a, ∑ b, p a * p b * ((X a - X b) * (Y a - Y b)))
        = ∑ a, ((∑ b, p a * p b * (X a * Y a)) - (∑ b, p a * p b * (X a * Y b))
          - (∑ b, p a * p b * (X b * Y a)) + (∑ b, p a * p b * (X b * Y b))) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner_eq a
    have hD1 : (∑ a, ∑ b, p a * p b * ((X a - X b) * (Y a - Y b)))
        = (∑ a, ∑ b, p a * p b * (X a * Y a))
          - (∑ a, ∑ b, p a * p b * (X a * Y b))
          - (∑ a, ∑ b, p a * p b * (X b * Y a))
          + (∑ a, ∑ b, p a * p b * (X b * Y b)) := by
      rw [h2, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [hD1, hT1, hT2, hT3, hT4]
    ring
  have hD_nonneg : 0 ≤ ∑ a, ∑ b, p a * p b * ((X a - X b) * (Y a - Y b)) :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hterm_nonneg a b))
  have hFKG : 0 ≤ S * EXY - EX * EY := by
    have h2 : 0 ≤ 2 * (S * EXY - EX * EY) := by
      rw [← hD_eq]
      exact hD_nonneg
    linarith
  have hSq : 0 ≤ EX * EY * (S - 1) ^ 2 :=
    mul_nonneg (mul_nonneg hEX_nonneg hEY_nonneg) (sq_nonneg _)
  have hSCov : S * (∑ z, p z * ((X z - EX) * (Y z - EY)))
      = (S * EXY - EX * EY) + EX * EY * (S - 1) ^ 2 := by
    rw [hCovEq]
    ring
  have hSCov_nonneg : 0 ≤ S * (∑ z, p z * ((X z - EX) * (Y z - EY))) := by
    rw [hSCov]
    exact add_nonneg hFKG hSq
  by_cases hS0 : S = 0
  · have hp0 : ∀ z, p z = 0 := by
      intro z
      by_contra hz
      have hpos : 0 < p z := lt_of_le_of_ne (hp z) (Ne.symm hz)
      have hle : p z ≤ ∑ w, p w :=
        Finset.single_le_sum (fun w _ => hp w) (Finset.mem_univ z)
      rw [← hS, hS0] at hle
      linarith
    have hCov0 : (∑ z, p z * ((X z - EX) * (Y z - EY))) = 0 := by
      rw [← Finset.sum_const_zero]
      apply Finset.sum_congr rfl
      intro z _
      rw [hp0 z, zero_mul]
    rw [hCov0]
  · have hSpos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
    by_contra hneg
    push Not at hneg
    have hlt : S * (∑ z, p z * ((X z - EX) * (Y z - EY))) < 0 :=
      mul_neg_of_pos_of_neg hSpos hneg
    linarith

/-- **Monotone latent curves give nonnegative item covariance.** Let the latent state space
`Z` be a finite linear order with law `pi`, and let the item curves `q z i ∈ [0, 1]` give
conditionally independent binary responses. If the curves of two distinct items `i` and `j`
are both monotone in the latent state, then the covariance of their response indicators under
the observed mixture law is nonnegative. This is the Fortuin--Kasteleyn--Ginibre inequality
(`fkg`) on the chain `Z`, transported to the observed law by
`latentMixture_coordinate_moments`. -/
theorem covariance_items_nonneg_of_monotone {Z ι : Type*} [Fintype Z] [LinearOrder Z]
    [Fintype ι] [DecidableEq ι] (pi : PMF Z) (q : Z → ι → ℝ)
    (hq0 : ∀ z i, 0 ≤ q z i) (hq1 : ∀ z i, q z i ≤ 1) {i j : ι} (hij : i ≠ j)
    (hi : Monotone fun z => q z i) (hj : Monotone fun z => q z j) :
    0 ≤ ProbabilityTheory.covariance (fun x : ι → Bool => if x i then (1 : ℝ) else 0)
      (fun x : ι → Bool => if x j then (1 : ℝ) else 0)
      (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure := by
  have hMix := latentMixture_coordinate_moments pi q hq0 hq1
  obtain ⟨h1, h2, h3⟩ := hMix
  have hEq := h3 i j hij
  rw [hEq]
  exact finiteCovariance_nonneg_of_monotone (fun z => (pi z).toReal) (fun z => q z i)
    (fun z => q z j) (fun z => by positivity) (fun z => hq0 z i) (fun z => hq0 z j) hi hj

end MathlibExt.Probability.Statistics.Measurement
