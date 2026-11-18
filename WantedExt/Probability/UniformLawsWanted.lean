/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Uniform laws of large numbers via Rademacher complexity: wishlist

Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Cambridge University
Press, 2019), Chapter 4, controls the uniform deviation `‖P_n - P‖_F = sup_{f ∈ F} |P_n f - P f|`
of empirical means over a function class `F` by its Rademacher complexity
`R_n(F) = E_{X, ε}[sup_{f ∈ F} |(1/n) ∑ εᵢ f(Xᵢ)|]`, where the `εᵢ` are independent uniform
signs. This module defines both quantities for a countable class, which makes the suprema
measurable, and records the symmetrization bound and the resulting uniform law as wanted
theorems.

The signs are averaged explicitly over the `2ⁿ` sign vectors `s : Fin n → Bool`, with
`εₖ = 1` when `s k` holds and `εₖ = -1` otherwise.
-/

open MeasureTheory

namespace MathlibExt.Probability.UniformLawsWanted

@[expose] public section

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {ι : Type*}

/-- The uniform deviation `‖P_n - P‖_F = sup_{f ∈ F} |(1/n) ∑ₖ f(xₖ) - E_P[f]|` of the empirical
means of a sample `x : Fin n → 𝓧` of size `n ≥ 1` from their expectations under a probability
measure `P`, for a class `F = {F i | i : ι}` (Wainwright, *High-Dimensional Statistics*, 2019,
§4.1.2). For a measure of infinite mass the expectation would be read as `0`, and for an empty
sample the empirical mean would be `0`. -/
noncomputable def uniformDeviation (P : Measure 𝓧) [IsProbabilityMeasure P] (F : ι → 𝓧 → ℝ)
    {n : ℕ} (_hn : 1 ≤ n) (x : Fin n → 𝓧) : ℝ :=
  ⨆ i, |(1 / (n : ℝ)) * ∑ k, F i (x k) - ∫ y, F i y ∂P|

/-- The Rademacher complexity `R_n(F) = E_{X, ε}[sup_{f ∈ F} |(1/n) ∑ₖ εₖ f(Xₖ)|]` of a class
`F = {F i | i : ι}` for `n ≥ 1` independent samples from a probability measure `P`, the
expectation over the uniform signs being the average over the `2ⁿ` sign vectors (Wainwright,
*High-Dimensional Statistics*, 2019, §4.2). For the zero measure or an empty sample it would be
`0` for every class. -/
noncomputable def rademacherComplexity (P : Measure 𝓧) [IsProbabilityMeasure P] (F : ι → 𝓧 → ℝ)
    {n : ℕ} (_hn : 1 ≤ n) : ℝ :=
  ∫ x, ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
      ⨆ i, |(1 / (n : ℝ)) * ∑ k, (if s k then (1 : ℝ) else -1) * F i (x k)|
    ∂(Measure.pi fun _ : Fin n => P)

/-- **Symmetrization** (Wainwright, *High-Dimensional Statistics*, 2019, §4.2, the symmetrization
step, upper bound in expectation): for a countable class of measurable functions bounded by `b` and
`n ≥ 1` independent
samples from a probability measure `P`, `E[‖P_n - P‖_F] ≤ 2 R_n(F)`. -/
public theorem_wanted integral_uniformDeviation_le_two_mul_rademacherComplexity
    (P : Measure 𝓧) [IsProbabilityMeasure P] [Countable ι] (F : ι → 𝓧 → ℝ)
    (hF : ∀ i, Measurable (F i)) {b : ℝ} (hb : ∀ i y, |F i y| ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, uniformDeviation P F hn x ∂(Measure.pi fun _ : Fin n => P) ≤
      2 * rademacherComplexity P F hn

/-- **Uniform law via Rademacher complexity** (Wainwright, *High-Dimensional Statistics*, 2019,
§4.2, the uniform law via Rademacher complexity): for a countable class of measurable functions
with `|f| ≤ b`, every `n ≥ 1` and
every `δ ≥ 0`, with probability at least `1 - exp (-n δ² / (2 b²))` over `n` independent samples
from a probability measure `P`, `‖P_n - P‖_F ≤ 2 R_n(F) + δ`. -/
public theorem_wanted uniformDeviation_le_two_mul_rademacherComplexity_add
    (P : Measure 𝓧) [IsProbabilityMeasure P] [Countable ι] (F : ι → 𝓧 → ℝ)
    (hF : ∀ i, Measurable (F i)) {b : ℝ} (hb0 : 0 < b) (hb : ∀ i y, |F i y| ≤ b) {n : ℕ}
    (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - Real.exp (-(n : ℝ) * δ ^ 2 / (2 * b ^ 2)) ≤
      (Measure.pi fun _ : Fin n => P).real
        {x | uniformDeviation P F hn x ≤ 2 * rademacherComplexity P F hn + δ}

end

end MathlibExt.Probability.UniformLawsWanted
