/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.HodgeRealization

@[expose] public section

/-!
# Tests for the Betti–de Rham realization

Global sections are evaluation at the whole space and are additive. The Betti
and de Rham complexes are global sections of the chosen injective resolutions,
and the Hodge filtration is the image of the cohomology of the cut
resolutions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AnalyticRealization
open MathlibExt.AlgebraicGeometry.HolomorphicDeRham
open MathlibExt.AlgebraicGeometry.HodgeRealization

namespace MathlibExtTest.AlgebraicGeometry.HodgeRealization

example (Z : TopCat.{0}) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z) :
    (globalSections ℚ Z).obj F = F.obj.obj (op ⊤) :=
  rfl

example (Z : TopCat.{0}) : (globalSections ℂ Z).Additive := inferInstance

variable {X : ComplexScheme} {d : ℕ} [AnalyticManifold X d]
  {D : HolomorphicDeRhamData X d} (R : BettiDeRhamResolution X d D)

example : bettiComplex R =
    ((globalSections ℚ (ComplexAnalytification.space X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R.rational.complex :=
  rfl

/-- The Hodge filtration is the range of the map induced on cohomology by the
cut resolution. -/
example (n p : ℤ) (x : ((deRhamComplex R).homology n)) :
    x ∈ hodgeFiltration R n p ↔
      x ∈ LinearMap.range (HomologicalComplex.homologyMap
        (((globalSections ℂ (ComplexAnalytification.space X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (R.cutMap p)) n).hom :=
  Iff.rfl

end MathlibExtTest.AlgebraicGeometry.HodgeRealization
