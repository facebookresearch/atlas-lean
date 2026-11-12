/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.ContrastInterval
/-!
# Tests for `MathlibExt.Probability.Statistics.LinearModel.ContrastInterval`

At `n = 2` the Cauchy (`t_1`) interval still covers; `n ≥ 2` gives positive degrees of
freedom; the universal set has full `t` mass. The non-rejected parameter slab has exact
coverage; a mass hypothesis is trivial at the `alpha = 1` endpoint; a negative threshold
gives an empty central set.
-/

namespace ProbabilityTheory.OneSampleChecks

open MeasureTheory ProbabilityTheory Real

/-- Use case: at `n = 2` the Cauchy (`t_1`) interval still covers. -/
example (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure ((2 : ℕ) - 1)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin 2 → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin 2 => gaussianReal μ v) P) :
    1 - α ≤ P.real {ω | |(∑ i, X ω i) / 2 - μ| ≤ c *
      √((∑ i, (X ω i - (∑ j, X ω j) / 2) ^ 2) / (((2 : ℕ) : ℝ) - 1)) / √(2 : ℝ)} := by
  exact one_sample_t_interval_coverage (le_refl 2) μ hv c hmass hα hX

/-- Positive degrees of freedom: `n ≥ 2` gives a positive `df`. -/
example (n : ℕ) (hn : 2 ≤ n) : 0 < n - 1 := by
  omega
/-- Endpoint: the universal set has full `t` mass, so `alpha = 1` always works. -/
example (d : ℕ) (hd : 0 < d) : (studentTMeasure d).real Set.univ = 1 := by
  have := isProbabilityMeasure_studentTMeasure hd
  exact probReal_univ
end ProbabilityTheory.OneSampleChecks

namespace MathlibExt.Probability.Statistics.LinearModel.SlabChecks

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

/-- Use case: the slab theorem applies as stated (no hidden side goals). -/
example {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    {a : k → ℝ} (ha : a ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (Fintype.card m - Fintype.card k)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    1 - α ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
      {y : m → ℝ | |tStatistic X a β y| ≤ c} :=
  contrast_slab_coverage hX hkm ha c hmass hα β hσ hε

/-- Use case: the contrast interval covers, exercising `contrast_interval_coverage`
including its interval-shaped conclusion and argument order. -/
example {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    {a : k → ℝ} (ha : a ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (Fintype.card m - Fintype.card k)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    1 - α ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
      {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
        √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
          ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)} :=
  contrast_interval_coverage hX hkm ha c hmass hα β hσ hε

/-- Endpoint: at `alpha = 1` the mass hypothesis is trivially satisfiable. -/
example (d : ℕ) (c : ℝ) : (studentTMeasure d).real (Set.Icc (-c) c) ≥ 1 - 1 := by
  rw [sub_self]
  exact ENNReal.toReal_nonneg

/-- Degenerate boundary: a negative `c` gives an empty central set, so a useful `c`
must satisfy `c ≥ 0`. -/
example (c : ℝ) (hc : c < 0) : Set.Icc (-c) c = ∅ := by
  exact Set.Icc_eq_empty (by linarith)

end MathlibExt.Probability.Statistics.LinearModel.SlabChecks