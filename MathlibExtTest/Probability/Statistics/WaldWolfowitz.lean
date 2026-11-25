/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WaldWolfowitz
public import MathlibExtTest.Probability.Statistics.WaldInequalities

/-!
# Tests for the Wald–Wolfowitz theorem

The instance of the tests of Wald's inequalities: observations with values in `Bool`, `P₀` the
fair coin and `P₁` the coin with `P₁ {true} = 1/3`. The tests compare the SPRT with
fixed-sample-size tests, the classical motivation of the theorem, and check the edge case of a
test that decides without observing.
-/

@[expose] public section

open MeasureTheory
open MathlibExtTest.Probability.Statistics.WaldInequalities
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.WaldWolfowitz

/-- The expected value of a constant time. -/
theorem lintegral_const_time {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) :
    ∫⁻ ω, ((show ℕ∞ from (fun _ : Ω => (n : WithTop ℕ)) ω) : ℝ≥0∞) ∂μ = n := by
  change ∫⁻ _, ((n : ℕ∞) : ℝ≥0∞) ∂μ = n
  simp

/-- The SPRT needs on average at most as many observations as the fixed-sample-size test with
`n` observations and rejection region `D`, as soon as `D` has error probabilities at most those
of the SPRT. -/
example {a b : ℝ} (ha : a < 0) (hb : 0 < b) (n : ℕ) {D : Set (ℕ → Bool)}
    (hD : MeasurableSet[observationFiltration Bool n] D)
    (hα : Measure.infinitePi (fun _ : ℕ => fairCoin) D ≤ Measure.infinitePi (fun _ : ℕ => fairCoin)
      (sprtAcceptOne fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b))
    (hβ : Measure.infinitePi (fun _ : ℕ => biasedCoin) Dᶜ ≤
      Measure.infinitePi (fun _ : ℕ => biasedCoin)
        (sprtAcceptZero fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b)) :
    ∫⁻ ω, ((show ℕ∞ from sprtTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => fairCoin) ≤ n ∧
      ∫⁻ ω, ((show ℕ∞ from sprtTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => biasedCoin) ≤ n := by
  have hT := isStoppingTime_const (observationFiltration Bool) n
  have hD' : MeasurableSet[hT.measurableSpace] D := by
    rwa [IsStoppingTime.measurableSpace_const]
  have h := sprt_wald_wolfowitz biasedCoin_ac fairCoin_ac fairCoin_ne_biasedCoin ha hb hT hD'
    ((lintegral_const_time _ n).trans_lt (ENNReal.natCast_lt_top n))
    ((lintegral_const_time _ n).trans_lt (ENNReal.natCast_lt_top n)) hα hβ
  exact ⟨h.1.trans (lintegral_const_time _ n).le, h.2.trans (lintegral_const_time _ n).le⟩

/-- A test that decides without observing cannot have error probabilities at most those of the
SPRT: the theorem would bound the expected sample size of the SPRT, which observes at least once,
by `0`. -/
example {a b : ℝ} (ha : a < 0) (hb : 0 < b) {D : Set (ℕ → Bool)}
    (hD : MeasurableSet[observationFiltration Bool 0] D) :
    ¬ (Measure.infinitePi (fun _ : ℕ => fairCoin) D ≤ Measure.infinitePi (fun _ : ℕ => fairCoin)
        (sprtAcceptOne fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b) ∧
      Measure.infinitePi (fun _ : ℕ => biasedCoin) Dᶜ ≤
        Measure.infinitePi (fun _ : ℕ => biasedCoin)
          (sprtAcceptZero fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b)) := by
  rintro ⟨hα, hβ⟩
  have hT := isStoppingTime_const (observationFiltration Bool) 0
  have hD' : MeasurableSet[hT.measurableSpace] D := by
    rwa [IsStoppingTime.measurableSpace_const]
  have h := (sprt_wald_wolfowitz biasedCoin_ac fairCoin_ac fairCoin_ne_biasedCoin ha hb hT hD'
    ((lintegral_const_time _ 0).trans_lt (ENNReal.natCast_lt_top 0))
    ((lintegral_const_time _ 0).trans_lt (ENNReal.natCast_lt_top 0)) hα hβ).1
  replace h := h.trans (lintegral_const_time _ 0).le
  have h1 : (1 : ℝ≥0∞) ≤ ∫⁻ ω,
      ((show ℕ∞ from sprtTime fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => fairCoin) := by
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Measure.infinitePi (fun _ : ℕ => fairCoin) := by simp
      _ ≤ _ := lintegral_mono fun ω => by
        have := le_hittingAfter (u := llrSum fairCoin biasedCoin biasedCoin_ac fairCoin_ac)
          (s := Set.Iic a ∪ Set.Ici b) (n := 1) ω
        exact (show (1 : ℝ≥0∞) = ((1 : ℕ∞) : ℝ≥0∞) by simp).trans_le (ENat.toENNReal_le.2 this)
  exact absurd (h1.trans h) (by simp)

end MathlibExtTest.Probability.Statistics.WaldWolfowitz
