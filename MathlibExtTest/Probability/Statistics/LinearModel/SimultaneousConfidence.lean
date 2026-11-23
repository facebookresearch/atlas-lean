/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.SimultaneousConfidence

/-!
# Tests for `MathlibExt.Probability.Statistics.LinearModel.SimultaneousConfidence`

The full-model use case (`C = 1`) covers the whole parameter vector; at `α = 1` the coverage
bound is vacuous and needs no mass input.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.LinearModel.SimultaneousConfidence

open Matrix MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.LinearModel
open MathlibExt.Probability.Statistics

/-- Use case (full model, `q = p`): with `C` the identity, the inverted set covers the
full parameter vector `β` with probability at least `1 - α`, by direct application of
`scheffe_coverage` at the `F(p, n-p)` mass hypothesis. `confSetOfTests` resolves through
the `MathlibExt.Probability.Statistics` open above. -/
theorem scheffe_coverage_full_model {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X))
    (hC : IsUnit ((1 : Matrix k k ℝ) * (Xᵀ * X)⁻¹ * (1 : Matrix k k ℝ)ᵀ))
    (hr : 0 < Fintype.card k)
    (hkm : Fintype.card k < Fintype.card m)
    (c : ℝ) {α : ℝ}
    (hmass : (snedecorFMeasure (Fintype.card k) (Fintype.card m - Fintype.card k)).real
      (Set.Icc 0 c) ≥ 1 - α)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    1 - α ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
      {y : m → ℝ | (1 : Matrix k k ℝ) *ᵥ β ∈ confSetOfTests
        (fun t : k → ℝ => {y : m → ℝ | c < fStatistic X 1 t y}) y} := by
  exact scheffe_coverage hX hC hr hkm c hmass hα β hσ hε

/-- Boundary: at `α = 1` the coverage lower bound is vacuous (`0 ≤ real`), using only
nonnegativity of the observation-law mass. `confSetOfTests` resolves through the
`MathlibExt.Probability.Statistics` open above. -/
theorem scheffe_coverage_alpha_one {m k r : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (hkm : Fintype.card k < Fintype.card m)
    (c : ℝ)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    (0 : ℝ) ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
      {y : m → ℝ | C *ᵥ β ∈ confSetOfTests
        (fun t : r → ℝ => {y : m → ℝ | c < fStatistic X C t y}) y} := by
  have hmass1 : (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real
      (Set.Icc 0 c) ≥ 1 - (1 : ℝ) := by
    rw [sub_self]
    exact measureReal_nonneg
  have hα1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h := scheffe_coverage hX hC hr hkm c hmass1 hα1 β hσ hε
  rwa [sub_self] at h

/-- The rejection sets inverted by `scheffe_coverage` are measurable for every hypothesized
contrast `t`, from the public `measurable_fStatistic`; no measurability hypothesis is needed. -/
example {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k] [Fintype r]
    [DecidableEq r] (X : Matrix m k ℝ) (C : Matrix r k ℝ) (c : ℝ) (t : r → ℝ) :
    MeasurableSet {y : m → ℝ | c < fStatistic X C t y} :=
  measurableSet_lt measurable_const (measurable_fStatistic X C t)

end MathlibExtTest.Probability.Statistics.LinearModel.SimultaneousConfidence
