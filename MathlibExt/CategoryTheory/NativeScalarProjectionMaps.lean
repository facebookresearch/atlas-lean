/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Computed native scalar projection maps

The projection is the mate of the prescribed inverse-image scalar
square under the two source-normalized native derived adjunctions.
The degree map uses the native quotient/cochain homology identifications
and the original right-derived scalar unit.

No comparison isomorphism or higher de Rham bundle is supplied as input.
The scalar square is fixed on every original module section and on every
native cochain unit.

References: Scholze, arXiv:1205.3463v2, Theorem 8.8 and Lemma 8.6;
native Mathlib adjunction, homology and right-derived operators, Apache 2.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeScalarProjectionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations

attribute [local instance] HasDerivedCategory.standard

namespace AdjunctionProjection

variable {C₁ D₁ C₂ D₂ : Type*}
  [Category* C₁] [Category* D₁] [Category* C₂] [Category* D₂]

/-- The actual mate is the native unit, source square and original counit. -/
def mate (L₁ : C₁ ⥤ D₁) (R₁ : D₁ ⥤ C₁) (a₁ : L₁ ⊣ R₁)
    (L₂ : C₂ ⥤ D₂) (R₂ : D₂ ⥤ C₂) (a₂ : L₂ ⊣ R₂)
    (FY : C₁ ⥤ C₂) (FX : D₁ ⥤ D₂) (square : FY ⋙ L₂ ⟶ L₁ ⋙ FX) (A : D₁) :
    FY.obj (R₁.obj A) ⟶ R₂.obj (FX.obj A) :=
  a₂.unit.app (FY.obj (R₁.obj A)) ≫
    R₂.map (square.app (R₁.obj A) ≫ FX.map (a₁.counit.app A))

end AdjunctionProjection

namespace DerivedCohomology

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [EnoughInjectives C]

local instance plusQuotientEssSurj : (DerivedCategory.Plus.Q (C := C)).EssSurj :=
  _root_.CategoryTheory.Functor.essSurj_of_iso (DerivedCategory.Plus.quotientCompQhIso C)

def cochainHomologyIso (K : CochainComplex.Plus C) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C i).obj (DerivedCategory.Plus.Q.obj K) ≅
      K.obj.homology i :=
  (DerivedCategory.homologyFunctor C i).mapIso ((DerivedCategory.Plus.QCompιIso C).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors C i).app K.obj

/-- Canonical cohomology comparison built from native cochain quotient factors and units. -/
def map (A : DerivedCategory.Plus C) (i : ℤ) :
    F.obj ((DerivedCategory.Plus.homologyFunctor C i).obj A) ⟶
      (DerivedCategory.Plus.homologyFunctor D i).obj (F.rightDerivedFunctorPlus.obj A) := by
  let K := DerivedCategory.Plus.Q.objPreimage A
  let e : DerivedCategory.Plus.Q.obj K ≅ A := DerivedCategory.Plus.Q.objObjPreimageIso A
  exact F.map ((DerivedCategory.Plus.homologyFunctor C i).map e.inv) ≫
    F.map (cochainHomologyIso K i).hom ≫
    ((K.obj.sc i).mapHomologyIso F).inv ≫
    (cochainHomologyIso (F.mapCochainComplexPlus.obj K) i).inv ≫
    (DerivedCategory.Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlusUnit.app K) ≫
    (DerivedCategory.Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlus.map e.hom)

end DerivedCohomology

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [UnivLE.{max u v, 1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  (SY TY : Sheaf J CommRingCat.{1}) (SX TX : Sheaf T CommRingCat.{1})
  (sy : SY ⟶ TY) (sx : SX ⟶ TX)
  (s : SY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj SX)
  (t : TY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj TX)

variable [(pushforward G SY SX s).IsRightAdjoint]
  [(pushforward G TY TX t).IsRightAdjoint]
  [(pushforward (𝟭 C) SY TY sy).IsRightAdjoint]
  [(pushforward (𝟭 D) SX TX sx).IsRightAdjoint]
  [EnoughInjectives (Modules SY)] [EnoughInjectives (Modules TY)]
  [EnoughInjectives (Modules SX)] [EnoughInjectives (Modules TX)]
  [PullbackSourceUnit G SY SX s] [PullbackSourceUnit G TY TX t]

abbrev scalarY := RingedDerivedCoefficientOperations.pullback (𝟭 C) SY TY sy
abbrev scalarX := RingedDerivedCoefficientOperations.pullback (𝟭 D) SX TX sx

local instance scalarYAdditive : (scalarY SY TY sy).Additive :=
  RingedDerivedCoefficientOperations.pullback_additive (G := 𝟭 C) (S := SY) (R := TY) (φ := sy)

local instance scalarXAdditive : (scalarX SX TX sx).Additive :=
  RingedDerivedCoefficientOperations.pullback_additive (G := 𝟭 D) (S := SX) (R := TX) (φ := sx)

/-- A scalar square with all ordinary sections and derived cochain units fixed. -/
structure SourceSquare where
  ring_square : sy ≫ t = s ≫
    (G.sheafPushforwardContinuous CommRingCat.{1} J T).map sx
  ordinary : scalarY SY TY sy ⋙ pullback G TY TX t ≅
    pullback G SY SX s ⋙ scalarX SX TX sx
  ordinary_units : ∀ (M : Modules SY) (U : Cᵒᵖ) (m : M.val.obj U),
    ((ordinary.hom.app M).val.app (G.op.obj U)).hom
      ((((adjunction G TY TX t).unit.app ((scalarY SY TY sy).obj M)).val.app U).hom
        ((((adjunction (𝟭 C) SY TY sy).unit.app M).val.app U).hom m)) =
    (((adjunction (𝟭 D) SX TX sx).unit.app ((pullback G SY SX s).obj M)).val.app
      (G.op.obj U)).hom ((((adjunction G SY SX s).unit.app M).val.app U).hom m)
  derived : (scalarY SY TY sy).rightDerivedFunctorPlus ⋙ derivedPullback G TY TX t ≅
    derivedPullback G SY SX s ⋙ (scalarX SX TX sx).rightDerivedFunctorPlus
  cochain_units : ∀ K : CochainComplex.Plus (Modules SY),
    (pullback G TY TX t).rightDerivedFunctorPlusUnit.app
      ((scalarY SY TY sy).mapCochainComplexPlus.obj K) ≫
      (derivedPullback G TY TX t).map
        ((scalarY SY TY sy).rightDerivedFunctorPlusUnit.app K) ≫
      derived.hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map (ordinary.hom.mapCochainComplexPlus.app K) ≫
      (scalarX SX TX sx).rightDerivedFunctorPlusUnit.app
        ((pullback G SY SX s).mapCochainComplexPlus.obj K) ≫
      (scalarX SX TX sx).rightDerivedFunctorPlus.map
        ((pullback G SY SX s).rightDerivedFunctorPlusUnit.app K)

variable (Q : SourceSquare G SY TY SX TX sy sx s t)
  (A : DerivedAdjunctionSource G SY SX s) (B : DerivedAdjunctionSource G TY TX t)

def projection (K : Derived SX) :
    (scalarY SY TY sy).rightDerivedFunctorPlus.obj ((derivedPushforward G SY SX s).obj K) ⟶
      (derivedPushforward G TY TX t).obj ((scalarX SX TX sx).rightDerivedFunctorPlus.obj K) :=
  AdjunctionProjection.mate (derivedPullback G SY SX s) (derivedPushforward G SY SX s) A.adj
    (derivedPullback G TY TX t) (derivedPushforward G TY TX t) B.adj
    (scalarY SY TY sy).rightDerivedFunctorPlus (scalarX SX TX sx).rightDerivedFunctorPlus
    Q.derived.hom K

variable [PreservesFiniteLimits (scalarY SY TY sy)] [PreservesFiniteColimits (scalarY SY TY sy)]

def degreeProjection (K : Derived SX) (i : ℤ) :
    (scalarY SY TY sy).obj (cohomology SY ((derivedPushforward G SY SX s).obj K) i) ⟶
      cohomology TY ((derivedPushforward G TY TX t).obj
        ((scalarX SX TX sx).rightDerivedFunctorPlus.obj K)) i :=
  DerivedCohomology.map (scalarY SY TY sy) ((derivedPushforward G SY SX s).obj K) i ≫
    (DerivedCategory.Plus.homologyFunctor (Modules TY) i).map
      (projection G SY TY SX TX sy sx s t Q A B K)

end MathlibExt.CategoryTheory.NativeScalarProjectionMaps
