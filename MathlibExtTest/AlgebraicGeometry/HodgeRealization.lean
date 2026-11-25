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
resolutions. A pure Betti Hodge realization forces this geometric filtration to
be antitone, and its map on cycles is determined by the chain comparison.
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

/-- The Hodge laws of a realization make the geometric filtration antitone. -/
example (n : ℤ) (H : PureBettiHodgeData R n) : Antitone (hodgeFiltration R n) := by
  intro p q hpq x hx
  have h := H.hodge.antitone hpq
  rw [H.filtration, H.filtration] at h
  have hy : H.complexIso.inv x ∈ (hodgeFiltration R n q).comap H.complexIso.hom.hom := by
    simpa using hx
  have hh := h hy
  change H.complexIso.hom (H.complexIso.inv x) ∈ hodgeFiltration R n p at hh
  simpa using hh

/-- The degreewise comparison is `ℚ`-linear. -/
example (n : ℤ) (q : ℚ) (x : (bettiComplex R).X n) :
    comparisonInDegree R n (q • x) = q • comparisonInDegree R n x :=
  map_smul _ q x

/-- The map on cycles of a realization is determined by the chain comparison. -/
example (n : ℤ) (H H' : PureBettiHodgeData R n) : H.cyclesMap = H'.cyclesMap := by
  ext z
  have hmono := (ModuleCat.mono_iff_injective ((deRhamComplex R).iCycles n)).1 inferInstance
  apply hmono
  rw [H.cycles_normalization, H'.cycles_normalization]

end MathlibExtTest.AlgebraicGeometry.HodgeRealization
