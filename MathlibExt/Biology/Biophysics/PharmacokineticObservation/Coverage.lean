/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# PK estimation coverage

Confidence coverage for a latent transfers through an estimand
map to any output set containing the transformed covered values:
estimation coverage is preserved by the PK observation map.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExt.Biology.Biophysics.PharmacokineticObservation.Coverage

/-- **Estimation coverage transfer.** If a confidence set `S` for a
latent `z` has coverage at least `1 - α` under a law `μ`
(`μ.real {ω | z ω ∈ S ω} ≥ 1 - α`), and an estimand map `g` satisfies
`z ω ∈ S ω → g (z ω) ∈ T ω` for an output set `T`, then the image
confidence statement also has coverage at least `1 - α`:
estimation coverage transfers through the PK estimand map. -/
lemma pk_est_coverage_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Set ℝ) (T : Ω → Set ℝ) (z : Ω → ℝ) (g : ℝ → ℝ) (α : ℝ)
    (hcover : ∀ ω, z ω ∈ S ω → g (z ω) ∈ T ω)
    (hcov : 1 - α ≤ μ.real {ω | z ω ∈ S ω}) :
    1 - α ≤ μ.real {ω | g (z ω) ∈ T ω} := by
  apply le_trans hcov
  apply measureReal_mono
  · intro ω h
    exact hcover ω h
  · exact measure_ne_top μ _

end MathlibExt.Biology.Biophysics.PharmacokineticObservation.Coverage
