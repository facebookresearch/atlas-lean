/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeModuleComparison

/-!
# Shifted cotensors as sphere-module functors

For a fixed finite-bijection index r and pointed space M, this file constructs a
sphere-module endofunctor with levels given by internal Hom from M into the levels indexed
by n ⊗ r. A natural isomorphism identifies its underlying symmetric sequence with this
shifted cotensor formula. The component of a module map is obtained by applying the same
internal Hom functor to its shifted level map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}

attribute [local instance] CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers

open PointedCGWH.SymmetricModulePresentation



/-- The target module functor retains the original full carrier, native shift,
scalar cotensor and complete original inverse carrier on all target arrows. -/
def targetModuleFunctor (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    OriginalModule.{u, v} ⥤ OriginalModule.{u, v} :=
  moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor.{u, v} r ⋙
    cotensor M ⋙ operatorToModule.{u, v}

private theorem identity_naturality {C : Type*} [Category C] {X Y : C}
    (b k : X ⟶ Y) (τ : X ⟶ X) (τ' : Y ⟶ Y)
    (hτ : τ = 𝟙 X) (hτ' : τ' = 𝟙 Y) (hk : k = b) :
    b ≫ τ' = τ ≫ k := by
  rw [hτ, hτ', Category.comp_id, Category.id_comp]
  exact hk.symm

set_option maxHeartbeats 500000 in
-- The component follows the complete native shift, cotensor and module reconstruction.
/-- Every actual native target arrow has the unchanged right-index scalar map. -/
theorem targetModuleFunctor_map_component (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    {N N' : OriginalModule.{u, v}} (f : N ⟶ N') (n : Operad.SmallFinBijGroupoid) :
    ((targetModuleFunctor r M).map f).hom.natTrans.app n =
      (ihom M).map (f.hom.natTrans.app (n ⊗ r)) := by
  let g := cotensorMap M ((PointedCGWH.SymmetricShift.functor.{u, v} r).map
    (toOperatorMorphism f))
  have hK := congrArg
    (fun z => z.natTrans.app n) (reconstructedModuleMap_hom g)
  have hRestrict := PointedCGWH.symmetricSequenceRestriction_component g n
  have hShift := PointedCGWH.SymmetricShift.functor_map_component r n (toOperatorMorphism f)
  have hBase := toOperatorMorphism_component f (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))
  have hCot := cotensorMap_component M
    ((PointedCGWH.SymmetricShift.functor.{u, v} r).map (toOperatorMorphism f))
    (PointedCGWH.symmetricOperatorObj.{u, v} n)
  exact hK.trans (hRestrict.trans (hCot.trans
    (congrArg (fun z => (ihom M).map z) (hShift.trans hBase))))

set_option maxHeartbeats 500000 in
-- Naturality compares the full reconstructed module arrows at every index.
/-- The original complete target sequence iso is natural for every native
shifted-cotensor target arrow, with its actual full module reconstruction. -/
def targetSequenceNatIso (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    Mod.forget (D := PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v} ⋙
        NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
      targetModuleFunctor r M ⋙
        Mod.forget (D := PointedCGWH.SymmetricSequence.{u, v})
          PointedCGWH.sphereSequence.{u, v} :=
  NatIso.ofComponents (fun N => (targetSequenceIso r M N).symm) (by
    intro N N' f
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext n
    let X := (ihom M).obj (N.X.functor.obj (n ⊗ r))
    let Y := (ihom M).obj (N'.X.functor.obj (n ⊗ r))
    let b : X ⟶ Y := (ihom M).map (f.hom.natTrans.app (n ⊗ r))
    let k : X ⟶ Y := ((targetModuleFunctor r M).map f).hom.natTrans.app n
    let τ : X ⟶ X := (targetSequenceIso r M N).inv.natTrans.app n
    let τ' : Y ⟶ Y := (targetSequenceIso r M N').inv.natTrans.app n
    have hτ : τ = 𝟙 X := targetSequenceIso_inv_component r M N n
    have hτ' : τ' = 𝟙 Y := targetSequenceIso_inv_component r M N' n
    have hk : k = b := targetModuleFunctor_map_component r M f n
    exact identity_naturality b k τ τ' hτ hτ' hk)

end NativeOmegaRecovery.NativeSymmetricFreeFunction
