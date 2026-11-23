/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations

@[expose] public section

/-!
# Tests for good filtrations

The lower bound and the generators of a good filtration are local: near each
point some filtration piece vanishes, and every section of a filtration piece
is, near each point, a combination of the local generators with operators of
the right order.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
open MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations
open MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves (finiteOperatorRing)

namespace MathlibExtTest.AlgebraicGeometry.GeometricDModuleFiltrations

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify
    ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective
    AddCommGrpCat.{0}]

/-- Near each point, the filtration piece below the local bound vanishes. -/
example (F : GoodFiltration E M) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ∃ p : ℤ, ∀ s : Section E M F.object U,
      InFiltration E M F.object F.term (p - 1) U s → s = 0 := by
  obtain ⟨U, hx, p, h⟩ := F.boundedBelow x
  exact ⟨U, hx, p, fun s hs ↦ h (p - 1) (by omega) U le_rfl s hs⟩

/-- Near each point, a section of a filtration piece over the generating open
is locally a combination of the generators. -/
example (F : GoodFiltration E M) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ∃ (r : ℕ) (degree : Fin r → ℤ)
      (generators : Fin r → Section E M F.object U), ∀ (p : ℤ) (s : Section E M F.object U),
      InFiltration E M F.object F.term p U s →
      ∃ (W : Opens M) (hW : W ≤ U), x ∈ W ∧
        ∃ (n : Fin r → ℕ)
          (P : Fin r → finiteOperatorRing ℂ M (coefficients E M) W),
          (∀ j, P j = 0 ∨ (OrderOn E M (P j) (n j) ∧ (n j : ℤ) + degree j ≤ p)) ∧
            restrictSection E M F.object hW s =
              ∑ j, act E M F.object (P j) (restrictSection E M F.object hW (generators j)) := by
  obtain ⟨U, hx, r, degree, generators, -, h⟩ := F.localGenerators x
  refine ⟨U, hx, r, degree, generators, fun p s hs ↦ ?_⟩
  obtain ⟨W, hW, hxW, n, P, hP, hs'⟩ := h U le_rfl p s hs x hx
  exact ⟨W, hW, hxW, n, P, hP, hs'⟩

end MathlibExtTest.AlgebraicGeometry.GeometricDModuleFiltrations

namespace MathlibExtTest.AlgebraicGeometry.HolomorphicCoefficientSheaves

open MathlibExt.AlgebraicGeometry

/-- Holomorphic functions are defined on complex manifolds; a bare charted
space, whose transition maps need not be holomorphic, is rejected. -/
example (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M] : True := by
  fail_if_success
    have := HolomorphicCoefficientSheaves.coefficientPresheaf ℂ M
  trivial

example (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ∞ M] :
    (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ :=
  HolomorphicCoefficientSheaves.coefficientPresheaf ℂ M

end MathlibExtTest.AlgebraicGeometry.HolomorphicCoefficientSheaves
