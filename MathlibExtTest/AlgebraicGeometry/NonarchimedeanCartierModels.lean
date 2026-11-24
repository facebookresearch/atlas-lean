/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels

/-!
# Tests for vertical Cartier models

Two central components of a vertical model whose valuations restrict to the same valuation of
`K(X)` and give the parameter the same order agree on every polynomial in the parameter: their
valuations are the same Gauss extension, so the model value is a function of the base valuation.
A valuation without discrepancy charts has chart supremum `⊥`, which is why entropy uses only
component valuations with charts; valuative semistability (`DVRGradedSectionFamilies`) is stated
with divisorial valuations and their intrinsic log discrepancies, and needs no charts. The model
polarization is a line bundle, and Monge--Ampère masses are only formed for semipositive models.
-/

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CenteredValuationSections
open MathlibExt.AlgebraicGeometry.MonomialModelRetractions
open MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels

variable {k : Type} [Field k] {n : ℕ} {P : LogPair k n} {L : P.variety.X.left.Modules}

/-- Central components with the same restriction and parameter order have the same order on
every nonzero polynomial in the parameter. -/
example (M : VerticalModel P L) {p q : PrimePoint M.model} (hp : p ∈ M.central)
    (hq : q ∈ M.central)
    (hres : ∀ a, M.model.X.left.ord (fieldMap M a) p.val = M.model.X.left.ord (fieldMap M a) q.val)
    (ht : M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val =
      M.model.X.left.ord (M.rationalParameter : FunctionField M.model) q.val)
    (f : Polynomial (FunctionField P.variety)) (hf : f ≠ 0) :
    M.model.X.left.ord (Polynomial.eval₂ (fieldMap M) (M.rationalParameter : FunctionField M.model)
        f) p.val =
      M.model.X.left.ord (Polynomial.eval₂ (fieldMap M)
        (M.rationalParameter : FunctionField M.model) f) q.val := by
  rw [show fieldMap M = dominantFieldMap _ M.dominant from rfl] at hres ⊢
  rw [M.gauss p hp f hf, M.gauss q hq f hf]
  simp only [hres, ht]

/-- A valuation without discrepancy charts has chart supremum `⊥`. -/
example (v : CenteredValuation P.variety) (h : ¬ HasDiscrepancyCharts v) :
    extendedDiscrepancy v = ⊥ := by
  rw [extendedDiscrepancy]
  convert sSup_empty
  refine iff_of_false ?_ (by simp)
  rintro ⟨C, -⟩
  exact h ⟨C⟩

/-- The model polarization is a line bundle. -/
example (M : VerticalModel P L) : IsLineBundle (modelPolarization M) :=
  modelPolarization_isLineBundle M

/-- A Monge--Ampère mass is the normalized intersection coefficient of a semipositive model. -/
example (M : VerticalModel P L) (hM : IsSemipositive M) (p : PrimePoint M.model)
    (hp : p ∈ M.central) :
    componentMass M hM p hp =
      (M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val : ℝ) *
        componentIntersection M p hp /
          ((M.exponent : ℝ) ^ n * (haveI := M.baseProper; baseVolume P (baseLine M))) :=
  rfl

/-- A model value is only formed at a central component, where the parameter vanishes. -/
example (M : VerticalModel P L) {p : PrimePoint M.model} (hp : p ∈ M.central) :
    0 < M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val :=
  (M.central_normalized p).mp hp
