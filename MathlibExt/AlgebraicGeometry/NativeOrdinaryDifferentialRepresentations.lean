/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts

/-!
# Ordinary structure modules and maps of original differential rings

The structure module is fixed on every actual coefficient section,
restriction and finite operator. Maps of ordinary ring monoids agree on
all original ring-sheaf sections with the specified ring morphism; beta
maps those exact native monoid maps.
Source: DK1311.2374v2 Sections4.10,5.2,8.2;
Mathlib56a005 native ring/module/sheafification/mapMon constructors, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeOrdinaryDifferentialRepresentations

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts
open IndDifferentialModuleModels RingedComplexCoefficientModels
open DifferentialOperatorSheaves

variable (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

/-- Every native coefficient and every finite operator, including all subopen restrictions, is retained. -/
structure StructureModuleSource where
  object : DModule ℂ M O
  sections : ∀ U : Opens M, object.val.obj (op U) ≃+ O.obj (op U)
  restriction : ∀ (U V : Opens M) (h : V ≤ U) (s : object.val.obj (op U)),
    sections V ((object.val.map (homOfLE h).op).hom s) = O.map (homOfLE h).op (sections U s)
  operator : ∀ (U : Opens M) (P : finiteOperatorRing ℂ M O U) (s : object.val.obj (op U)),
    sections U (((toSheafify (Opens.grothendieckTopology M) (operatorPresheaf ℂ M O)).app
      (op U)).hom P • s) = P.val.val ⟨U, le_refl U⟩ (sections U s)

variable (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [CX : IndSpaceSource X]
  (R S : TopCat.Sheaf RingCat.{0} X)
  [RS : BetaRingSource X R] [SS : BetaRingSource X S] (φ : R ⟶ S)

def PreservesComplexConstants : Prop :=
  ∀ (U : Opens X) (c : ℂ),
    letI : Algebra ℂ (R.obj.obj (op U)) :=
      ComplexRingSheafSource.algebra (X := X) (R := R) U
    letI : Algebra ℂ (S.obj.obj (op U)) :=
      ComplexRingSheafSource.algebra (X := X) (R := S) U
    (φ.hom.app (op U)).hom (algebraMap ℂ (R.obj.obj (op U)) c) =
      algebraMap ℂ (S.obj.obj (op U)) c

/-- The native monoid morphism has the original ring morphism as its map on every actual section. -/
structure OrdinaryRingMapSource where
  map : ordinaryRing X R RS.coefficient RS.monoid ⟶ ordinaryRing X S SS.coefficient SS.monoid
  value : ∀ (U : Opens X) (a : R.obj.obj (op U)),
    (map.hom.hom.app (op U)).hom a = (φ.hom.app (op U)).hom a

def betaRingMap (F : OrdinaryRingMapSource X R S φ) : betaRing X R ⟶ betaRing X S := by
  change (IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta).mapMon.obj
      (ordinaryRing X R RS.coefficient RS.monoid) ⟶
    (IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta).mapMon.obj
      (ordinaryRing X S SS.coefficient SS.monoid)
  exact (IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta).mapMon.map F.map

end MathlibExt.AlgebraicGeometry.NativeOrdinaryDifferentialRepresentations
