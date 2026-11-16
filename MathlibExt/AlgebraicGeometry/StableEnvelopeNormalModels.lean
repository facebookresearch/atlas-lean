/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusAttractingOrderModels
public import MathlibExt.AlgebraicGeometry.ResidualTorusDegreeModels

/-!
# The full normal-weight arrangement and its chamber eigensums

The hyperplanes enumerate every actual nonzero normal character from
every connected fixed component. The component chamber cocharacters
are the same original global group-scheme map. Negative inclusions
are computed from the original tangent eigensummand inclusions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.StableEnvelopeNormalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusDifferentialGeometryModels
open TorusPolynomialDegreeModels TorusFixedSchemeModels

theorem componentFixed {A X : Over base} [GrpObj A] [ModObj A X]
    {F : FixedSchemeModel A X} (Z : FixedComponent A X F) :
    FixedPoint A X (Z.toAmbient A X) :=
  fixedReindex A X Z.inclusion F.inclusion F.fixed

/-- The full arrangement contains exactly the occurring normal characters of all components. -/
structure NormalFamily {A : Over base} [GrpObj A] (M : TorusModel A)
    (X : Over base) [ModObj A X] (F : FixedSchemeModel A X) (Z : FixedComponents A X F) where
  normal : ∀ j : Fin Z.count,
    NormalGeometry M ((Z.component j).toAmbient A X) (componentFixed (Z.component j))
  componentRoots : ∀ j : Fin Z.count, NormalRoots (normal j)
  roots : RootCoordinates M
  index : Fin roots.count ≃ Σ j : Fin Z.count, Fin (componentRoots j).roots.count
  character : ∀ k : Fin roots.count,
    roots.character k = (componentRoots (index k).1).roots.character (index k).2

variable {A X F : Over base} [GrpObj A] [ModObj A X]
  {M : TorusModel A} {i : F ⟶ X} {hi : FixedPoint A X i} {N : NormalGeometry M i hi}
  (R : NormalRoots N) (C : Chamber R.roots) (L : ChamberCocharacter C)

/-- The chamber-negative inclusion uses the same original tangent summand maps. -/
def negativeInclusion : negativeNormal R C L ⟶
    (Scheme.Modules.pullback i.left).obj (Tangent X) := by
  classical
  letI := Fintype.ofFinite {j : Fin R.roots.count // (L.paired j).weight < 0}
  exact biproduct.desc (fun j : {j : Fin R.roots.count // (L.paired j).weight < 0} =>
    N.weights.inclusion (R.index j.1).1)

/-- The local chamber uses precisely the global chosen one-parameter subgroup. -/
structure ComponentChamber {A : Over base} [GrpObj A] {M : TorusModel A}
    {Roots : RootCoordinates M} (C : Chamber Roots) (L : ChamberCocharacter C)
    {X F : Over base} [ModObj A X] {i : F ⟶ X} {hi : FixedPoint A X i}
    {N : NormalGeometry M i hi} (R : NormalRoots N) where
  chamber : Chamber R.roots
  cocharacter : ChamberCocharacter chamber
  original : cocharacter.map = L.map
  polarization : Polarization R chamber cocharacter
  halfRank : 2*negativeRank R chamber cocharacter = normalRank R

end MathlibExt.AlgebraicGeometry.StableEnvelopeNormalModels
