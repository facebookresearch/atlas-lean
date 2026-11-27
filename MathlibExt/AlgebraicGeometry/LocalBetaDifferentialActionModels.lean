/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
public import MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
public import MathlibExt.CategoryTheory.NativeBetaSectionActions

/-!
# Actual open restriction and local-End beta-ring actions

The restricted module is mapped by the original compact-Yoneda inverse
image, preserving both native actions. Every ordinary coefficient section
map is fixed by the original sheaf inverse-image adjunction unit and all
unit-section values. Its beta image induces the actual local endomorphism
through the native bimodule action.

Source: DK1311.2374v2 Section4.10; Mathlib56a005 native inverse image,
adjunction unit, monoidal mapMon and Bimod action, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LocalBetaDifferentialActionModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafAlphaBetaModels
open IndSheafMonoidalModels RingedComplexCoefficientModels BetaDifferentialRingModels
open IndDifferentialModuleModels NativeIndDifferentialContexts IndSheafInverseImageModels
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
open MathlibExt.CategoryTheory.NativeBetaSectionActions

variable (X : TopCat.{0}) (U : Opens X)

def openInclusion : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def pulledRing (R : TopCat.Sheaf RingCat.{0} X) : TopCat.Sheaf RingCat.{0} (TopCat.of U) :=
  (TopCat.Sheaf.pullback RingCat.{0} (openInclusion X U)).obj R

/-- The original pullback unit section followed by restriction to the actual subopen. -/
def pulledSection (R : TopCat.Sheaf RingCat.{0} X) (a : R.obj.obj (op U)) (V : Opens U) :
    (pulledRing X U R).obj.obj (op V) :=
  let initial := (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{0}
    (openInclusion X U)).unit.app R).hom.app (op U)).hom a
  ((pulledRing X U R).obj.map (homOfLE (show V ≤ (Opens.map (openInclusion X U)).obj U from
    fun x _ => x.property)).op).hom initial

variable
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [CX : IndSpaceSource X]
  [HasSheafify (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of U)] [CU : IndSpaceSource (TopCat.of U)]
  (R S : TopCat.Sheaf RingCat.{0} X)
  [BetaRingSource X R] [BetaRingSource X S]
  [LR : BetaRingSource (TopCat.of U) (pulledRing X U R)]
  [LS : BetaRingSource (TopCat.of U) (pulledRing X U S)]

structure OrdinaryRingSectionSource where
  sectionMap : ∀ a : R.obj.obj (op U), 𝟙_ (OrdinarySheaf ℂ (TopCat.of U)) ⟶
    (ordinaryRing (TopCat.of U) (pulledRing X U R) LR.coefficient LR.monoid).X
  value : ∀ (a : R.obj.obj (op U)) (V : Opens U) (c : ℂ),
    letI : Algebra ℂ ((pulledRing X U R).obj.obj (op V)) :=
      ComplexRingSheafSource.algebra (X := TopCat.of U) (R := pulledRing X U R) V
    (sectionMap a).hom.app (op V) (sourceUnitSection ℂ (TopCat.of U) V c) =
      algebraMap ℂ ((pulledRing X U R).obj.obj (op V)) c * pulledSection X U R a V

variable (F : Bimod (betaRing X R) (betaRing X S))

/-- The ordinary pullback of a ring's coefficient monoid is identified with the coefficient monoid
of the pulled ring, on actual sections by the pullback adjunction unit. -/
structure OrdinaryRingRestriction (T : TopCat.Sheaf RingCat.{0} X) [BetaRingSource X T]
    [LT : BetaRingSource (TopCat.of U) (pulledRing X U T)]
    [(TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (openInclusion X U)).Monoidal] where
  comparison : (TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (openInclusion X U)).mapMon.obj
      (ordinaryRing X T (BetaRingSource.coefficient (X := X) (R := T))
        (BetaRingSource.monoid (X := X) (R := T))) ≅
    ordinaryRing (TopCat.of U) (pulledRing X U T) LT.coefficient LT.monoid
  unitValue : ∀ (V : Opens X) (a : T.obj.obj (op V)),
    (comparison.hom.hom.hom.app (op ((Opens.map (openInclusion X U)).obj V))).hom
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℂ) (openInclusion X U)).unit.app
        (ringCoefficientSheaf X T (BetaRingSource.coefficient (X := X) (R := T)))).hom.app
          (op V)).hom a) =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{0} (openInclusion X U)).unit.app
        T).hom.app (op V)).hom a

/-- Both local actions are the prescribed monoidal map of the actual inverse image. The local ring
comparisons are not free data: they are built from a monoidal comparison of `β` with inverse image
and from the ordinary ring restrictions, which are fixed on actual sections. -/
structure LocalRestrictedModuleSource (_F : Bimod (betaRing X R) (betaRing X S)) where
  ordinary : OrdinaryIndSource ℂ (TopCat.of U)
  inverse : IndInverseImageSource ℂ (openInclusion X U) ordinary
  [monoidal : (indInverseImage ℂ (openInclusion X U) ordinary inverse).Monoidal]
  mapping : BimoduleMappingSource (indInverseImage ℂ (openInclusion X U) ordinary inverse)
    (betaRing X R) (betaRing X S)
  [ordinaryMonoidal : (TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (openInclusion X U)).Monoidal]
  natural : IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta ⋙
      indInverseImage ℂ (openInclusion X U) ordinary inverse ≅
    TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (openInclusion X U) ⋙
      IndSheafAlphaBetaModels.beta ℂ (TopCat.of U) CU.alpha CU.beta
  [naturalMonoidal : NatTrans.IsMonoidal natural.hom]
  leftRestriction : OrdinaryRingRestriction X U R
  rightRestriction : OrdinaryRingRestriction X U S

variable (L : LocalRestrictedModuleSource X U R S F)

/-- The local ring comparison for a ring restricted to `U`, assembled from the monoidal comparison
of `β` with inverse image and the ordinary ring restriction. -/
def LocalRestrictedModuleSource.ringComparison (T : TopCat.Sheaf RingCat.{0} X)
    [BetaRingSource X T] [LT : BetaRingSource (TopCat.of U) (pulledRing X U T)]
    (Q : letI := L.ordinaryMonoidal; OrdinaryRingRestriction X U T) :
    letI := L.monoidal
    betaRing (TopCat.of U) (pulledRing X U T) ≅
      (indInverseImage ℂ (openInclusion X U) L.ordinary L.inverse).mapMon.obj (betaRing X T) :=
  letI := L.monoidal
  letI := L.ordinaryMonoidal
  letI := L.naturalMonoidal
  ((Functor.mapMonCompIso (F := IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta)
      (G := indInverseImage ℂ (openInclusion X U) L.ordinary L.inverse)).symm.app
        (ordinaryRing X T (BetaRingSource.coefficient (X := X) (R := T))
          (BetaRingSource.monoid (X := X) (R := T))) ≪≫
    (Functor.mapMonNatIso L.natural).app
      (ordinaryRing X T (BetaRingSource.coefficient (X := X) (R := T))
        (BetaRingSource.monoid (X := X) (R := T))) ≪≫
    (Functor.mapMonCompIso (F := TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (openInclusion X U))
      (G := IndSheafAlphaBetaModels.beta ℂ (TopCat.of U) CU.alpha CU.beta)).app
        (ordinaryRing X T (BetaRingSource.coefficient (X := X) (R := T))
          (BetaRingSource.monoid (X := X) (R := T))) ≪≫
    (IndSheafAlphaBetaModels.beta ℂ (TopCat.of U) CU.alpha CU.beta).mapMon.mapIso
      Q.comparison).symm

/-- The left local ring comparison. -/
abbrev LocalRestrictedModuleSource.leftRing :
    letI := L.monoidal
    betaRing (TopCat.of U) (pulledRing X U R) ≅
      (indInverseImage ℂ (openInclusion X U) L.ordinary L.inverse).mapMon.obj (betaRing X R) :=
  LocalRestrictedModuleSource.ringComparison X U R S F L R L.leftRestriction

/-- The right local ring comparison. -/
abbrev LocalRestrictedModuleSource.rightRing :
    letI := L.monoidal
    betaRing (TopCat.of U) (pulledRing X U S) ≅
      (indInverseImage ℂ (openInclusion X U) L.ordinary L.inverse).mapMon.obj (betaRing X S) :=
  LocalRestrictedModuleSource.ringComparison X U R S F L S L.rightRestriction

def restrictedUnderlying : IndSheaf ℂ (TopCat.of U) :=
  letI := L.monoidal
  (L.mapping.functor.obj F).X

def localLeftEnd (E : OrdinaryRingSectionSource X U R) (a : R.obj.obj (op U)) :
    restrictedUnderlying X U R S F L ⟶ restrictedUnderlying X U R S F L :=
  letI := L.monoidal
  leftSectionEnd (IndSheafAlphaBetaModels.beta ℂ (TopCat.of U) CU.alpha CU.beta)
    (ordinaryRing (TopCat.of U) (pulledRing X U R) LR.coefficient LR.monoid)
    _ _ L.leftRing (L.mapping.functor.obj F) (E.sectionMap a)

def localRightEnd (E : OrdinaryRingSectionSource X U S) (a : S.obj.obj (op U)) :
    restrictedUnderlying X U R S F L ⟶ restrictedUnderlying X U R S F L :=
  letI := L.monoidal
  rightSectionEnd (IndSheafAlphaBetaModels.beta ℂ (TopCat.of U) CU.alpha CU.beta)
    (ordinaryRing (TopCat.of U) (pulledRing X U S) LS.coefficient LS.monoid)
    _ _ L.rightRing (L.mapping.functor.obj F) (E.sectionMap a)

end MathlibExt.AlgebraicGeometry.LocalBetaDifferentialActionModels
