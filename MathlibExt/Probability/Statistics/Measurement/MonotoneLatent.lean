/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.LatentMoments
public import Mathlib.Probability.Moments.Covariance
public import MathlibExt.Analysis.MonotonePowerSumInequalities

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
    (p X Y : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1)
    (hXm : Monotone X) (hYm : Monotone Y) :
    0 ≤ MathlibExt.Probability.FiniteProbability.covariance p X Y := by
  rw [MathlibExt.Probability.FiniteProbability.covariance_eq_sub hp1 X Y]
  simp only [MathlibExt.Probability.FiniteProbability.expectation]
  have hMono : MonovaryOn X Y (↑(Finset.univ : Finset Z) : Set Z) := by
    intro a _ b _ hlt
    rcases le_total a b with hab | hba
    · exact hXm hab
    · have hle : Y b ≤ Y a := hYm hba
      have hlt' : Y a < Y a := lt_of_lt_of_le hlt hle
      exact absurd hlt' (lt_irrefl _)
  have hCheb := MetaMathlibExt.MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul
    (f := X) (g := Y) (w := p) (s := Finset.univ) hMono (fun i _ => hp i)
  have hp1' : (∑ i ∈ (Finset.univ : Finset Z), p i) = 1 := hp1
  have hmass : (∑ i ∈ (Finset.univ : Finset Z), p i * X i * Y i)
      = ∑ z, p z * (X z * Y z) := by
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hp1', hmass] at hCheb
  have hex : (∑ x, p x * X x) = ∑ i ∈ (Finset.univ : Finset Z), p i * X i := rfl
  have hey : (∑ x, p x * Y x) = ∑ i ∈ (Finset.univ : Finset Z), p i * Y i := rfl
  rw [hex, hey]
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
    (fun z => q z j) (fun z => by positivity)
    (MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one pi) hi hj

end MathlibExt.Probability.Statistics.Measurement
