/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.WaldEquation

/-!
# Diagonal terms in Wald's second equation

The stopped sum of squares is integrable and satisfies
`E[∑_{i<T} Xᵢ²] = E[X₀²] · E[T]`.

## Source and proof

This formalizes `wald_diagonal_terms` and `integrable_stopped_sum_sq_diag`
from `v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean`.
As in v1, apply Wald's equation to `Y i ω = (X i ω)²`. The current canonical
`MeasureTheory.wald_equation` already assumes only coordinate/filtration
independence. Its integrability corollary reuses the same summable `L¹` series.
Squaring preserves identical distribution and shrinks each coordinate's comap.
The supplied square-integrability premise is precisely integrability of `Y 0`.

In v1, both declarations additionally assume `iIndepFun X μ`, and
`wald_diagonal_terms` also assumes `Integrable (X 0) μ`. The statements here
omit those redundant premises and are stronger than the corresponding v1 statements.
No adaptedness or extra measurability premise is required.
The generic canonical proof supplies the layer-cake, factorization and summability
machinery; this module contains only the squared-sequence bridge.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.WaldDiagonalTerms

private theorem indep_sq_of_filtration
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    {f : Filtration ℕ m}
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ) :
    ∀ k, Indep (MeasurableSpace.comap (fun ω => (X k ω)^2) inferInstance) (f k) μ :=
  fun k => indep_of_indep_of_le_left (hXf k)
    (MeasurableSpace.comap_le_comap_of_eq_comp (fun x : ℝ => x^2)
      (measurable_id.pow_const 2) rfl)

/-- The stopped sum of squares is integrable under the stated diagonal hypotheses. -/
theorem integrable_stopped_sum_sq_diag
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    Integrable (fun ω => ∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) μ :=
  wald_integrable_stopped_sum (X := fun i ω => (X i ω)^2)
    (fun i j => (hX_iid i j).comp (measurable_id.pow_const 2)) hX_sq_int hT
    (indep_sq_of_filtration hXf) hT_int

/-- Wald's equation applied to the squared increments gives the diagonal identity. -/
theorem wald_diagonal_terms
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) ∂μ =
      (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) :=
  wald_equation (X := fun i ω => (X i ω)^2)
    (fun i j => (hX_iid i j).comp (measurable_id.pow_const 2)) hX_sq_int hT
    (indep_sq_of_filtration hXf) hT_int

end MathlibExt.Probability.WaldDiagonalTerms
