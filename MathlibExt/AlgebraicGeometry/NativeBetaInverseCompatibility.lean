/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndModuleInverseModels
public import MathlibExt.AlgebraicGeometry.PulledBetaRingModels
public import MathlibExt.AlgebraicGeometry.NativeOrdinaryDifferentialRepresentations

/-!
# Canonical ring comparison from original beta/inverse compatibility

The comparison is the component of one monoidal natural isomorphism on
all ordinary sheaves, combined with the native mapMon composition maps.
The ordinary pulled-ring component is fixed on every original section
by the actual ordinary sheaf pullback units. This excludes independently
chosen ring automorphisms when identifying the projected X/P rings.

Source: DK1311.2374v2 Sections2.2,4.10;
Mathlib56a005 native monoidal natural transformations/mapMon, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeBetaInverseCompatibility

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeIndModuleInverseModels
open IndDifferentialModuleModels BetaDifferentialRingModels PulledBetaRingModels

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [CompactSheafSource ℂ Y]
  [CX : IndSpaceSource X] [CY : IndSpaceSource Y]
  (I : InverseMonoidalSource f)

local instance compatibilityInverseBraided : (originalInverse f I).Braided := I.braided

/-- A braided monoidal structure on the inverse image functor along the continuous map `f` for
sheaves of $\mathbb{C}$-vector spaces, with their sheafified tensor products. -/
class OrdinaryInverseMonoidalSource where
  [braided : (TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) f).Braided]

attribute [instance_reducible, instance] OrdinaryInverseMonoidalSource.braided

variable [OrdinaryInverseMonoidalSource f]

structure BetaInverseNaturalSource where
  comparison : (IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta ⋙ originalInverse f I) ≅
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) f ⋙
      IndSheafAlphaBetaModels.beta ℂ Y CY.alpha CY.beta)
  [monoidal : NatTrans.IsMonoidal comparison.hom]

variable (R : TopCat.Sheaf RingCat.{0} X) [RS : BetaRingSource X R]
  [YS : PulledBetaRingSource f R]

structure OrdinaryRingPullbackSource where
  comparison : (TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) f).mapMon.obj
    (ordinaryRing X R RS.coefficient RS.monoid) ≅
      ordinaryRing Y (pullbackRing f R) YS.source.coefficient YS.source.monoid
  unitValue : ∀ (U : Opens X) (a : R.obj.obj (op U)),
    (comparison.hom.hom.hom.app (op ((Opens.map f).obj U))).hom
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℂ) f).unit.app
        (ringCoefficientSheaf X R RS.coefficient)).hom.app (op U)).hom a) =
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{0} f).unit.app R).hom.app (op U)).hom a

def inverseBetaRingComparison (N : BetaInverseNaturalSource f I)
    (P : OrdinaryRingPullbackSource f R) :
    inverseRing f I (betaRing X R) ≅ betaRing Y (pullbackRing f R) :=
  letI := N.monoidal
  ((Functor.mapMonCompIso (F := IndSheafAlphaBetaModels.beta ℂ X CX.alpha CX.beta)
      (G := originalInverse f I)).symm.app (ordinaryRing X R RS.coefficient RS.monoid)) ≪≫
    (Functor.mapMonNatIso N.comparison).app (ordinaryRing X R RS.coefficient RS.monoid) ≪≫
    (Functor.mapMonCompIso (F := TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) f)
      (G := IndSheafAlphaBetaModels.beta ℂ Y CY.alpha CY.beta)).app
        (ordinaryRing X R RS.coefficient RS.monoid) ≪≫
    (IndSheafAlphaBetaModels.beta ℂ Y CY.alpha CY.beta).mapMon.mapIso P.comparison

end MathlibExt.AlgebraicGeometry.NativeBetaInverseCompatibility
