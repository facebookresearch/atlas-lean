/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.TargetModule
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Factories
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftCotensorAction
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.CotensorSequence
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftSequence
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Original
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Native

/-!
# Function-spectrum comparison for free symmetric modules

Identifies the internal Hom from a free sphere module at a finite-set index with the shifted
cotensor operator diagram. Constructs the whole module isomorphism and computes both maps at
every finite-set level.
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

attribute [local instance] PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds


/-- The unchanged original sphere Day-module category. -/
abbrev OriginalModule := Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v}

/-- Sharing the native witnesses preserves the old original module carrier type. -/
theorem originalModule_eq_original : OriginalModule.{u, v} =
    (letI : MonoidalCategory PointedCGWH.SymmetricSequence.{u, v} :=
       PointedCGWH.originalSymmetricSequenceMonoidal.{u, v}
     Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v}) := rfl

/-- The unchanged full native symmetric operator carrier. -/
abbrev NativeCarrier :=
  EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

private abbrev freeSequence (r : I) (M : V.{u, v}) : Sequence.{u, v} :=
  .mk ((evaluationLeftAdjoint V.{u, v} r).obj M)

/-- The actual original module internal Hom from the original ordinary free source. -/
def originalHom (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) : OriginalModule.{u, v} :=
  FullFreeFunctionModuleComparison.homModule (I := Operad.SmallFinBijGroupoid)
    (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N

/-- The shared producer retains the literal original module internal Hom,
with the original free sequence and every native module field. -/
theorem originalHom_eq_originalInternalHom (r : Operad.SmallFinBijGroupoid)
    (M : PointedCGWH.{u, v}) (N : OriginalModule.{u, v}) :
    originalHom r M N =
      (Mod.internalHom PointedCGWH.sphereSequenceCommMon.{u, v}
        ((Mod.free PointedCGWH.sphereSequence.{u, v}).obj
          ((DayFunctor.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj M))))).obj N := by
  dsimp only [originalHom, FullFreeFunctionModuleComparison.homModule, freeSequence]
  congr 4

/-- The target uses the existing full native right shift and actual scalar cotensor. -/
def target (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) : NativeCarrier.{u, v} :=
  cotensorObject M ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj (toOperatorFunctor N))

/-- Every original ordinary index map identifies the complete target sequence
with the unchanged right-tensor/internal-Hom sequence. -/
def targetSequenceIso (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) (N : OriginalModule.{u, v}) :
    (PointedCGWH.symmetricSequenceRestriction.{u, v}).obj (target r M N) ≅
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X := by
  let F : Operad.SmallFinBijGroupoid ⥤ PointedCGWH.{u, v} :=
    ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj (target r M N)).functor
  let G : Operad.SmallFinBijGroupoid ⥤ PointedCGWH.{u, v} := tensorRight r ⋙ N.X.functor ⋙ ihom M
  let e : F ≅ G := NatIso.ofComponents
    (fun n => Iso.refl ((ihom M).obj (N.X.functor.obj (n ⊗ r)))) (by
      intro n k f
      change ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj
          (cotensorObject M ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj
            (toOperatorFunctor N)))).functor.map f ≫ 𝟙 _ =
        𝟙 _ ≫ (ihom M).map (N.X.functor.map (f ▷ r))
      rw [Category.comp_id, Category.id_comp,
        NativeOmegaPreparation.NativeSymmetricCotensorSequence.map,
        NativeOmegaPreparation.NativeSymmetricShiftSequence.map,
        symmetricSequenceRestriction_forward_map]
      rfl)
  exact (DayFunctor.equiv Operad.SmallFinBijGroupoid PointedCGWH.{u, v}).inverse.mapIso e

/-- The target comparison keeps the original complete level identity. -/
theorem targetSequenceIso_hom_component (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (targetSequenceIso r M N).hom.natTrans.app n =
      𝟙 ((ihom M).obj (N.X.functor.obj (n ⊗ r))) := rfl

/-- The inverse target comparison keeps the same original level identity. -/
theorem targetSequenceIso_inv_component (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (targetSequenceIso r M N).inv.natTrans.app n =
      𝟙 ((ihom M).obj (N.X.functor.obj (n ⊗ r))) := rfl

set_option maxHeartbeats 1000000 in
-- The full native free comparison checks its complete module and enriched evaluation data.
/-- Original free-unit/equalizer/end evaluation provides both exact native
sequence maps, retaining the original beta_(r,n). -/
def sequenceIso (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) (N : OriginalModule.{u, v}) :
    (originalHom r M N).X ≅ (reconstructedModule (target r M N)).X := by
  let e : (originalHom r M N).X ≅
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X :=
    FullFreeFunctionPair.comparison (I := Operad.SmallFinBijGroupoid)
      (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N
  exact e ≪≫ (targetSequenceIso r M N).symm

/-- Every original native pair action is the exact frozen shifted-cotensor action. -/
theorem target_pair (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) (a n : Operad.SmallFinBijGroupoid) :
    reconstructedPairAction (target r M N) a n =
      FullFreeFunctionPair.targetAction (I := Operad.SmallFinBijGroupoid)
        (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N a n := by
  have h := NativeOmegaPreparation.NativeSymmetricShiftCotensorAction.pair_action
    (toOperatorFunctor N) M r a n
  rw [reconstructedPairAction_forward, symmetricSequenceRestriction_forward_map] at h
  exact h

set_option maxHeartbeats 1000000 in
-- The full native free comparison checks its complete module and enriched evaluation data.
/-- The original full free-unit/end/braid forward map on the actual two native levels. -/
def forwardLevel (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (originalHom r M N).X.functor.obj n ⟶
      (reconstructedModule (target r M N)).X.functor.obj n :=
  (FullFreeFunctionPair.comparison (I := Operad.SmallFinBijGroupoid)
    (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N).hom.natTrans.app n

set_option maxHeartbeats 1000000 in
-- The full native free comparison checks its complete module and enriched evaluation data.
/-- The original full free-extension/end-extension inverse on the actual native levels. -/
def inverseLevel (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (reconstructedModule (target r M N)).X.functor.obj n ⟶
      (originalHom r M N).X.functor.obj n :=
  (FullFreeFunctionPair.comparison (I := Operad.SmallFinBijGroupoid)
    (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N).inv.natTrans.app n


private theorem identity_square {C : Type*} [Category C] [MonoidalCategory C]
    (B X Y : C) (p q : B ⊗ X ⟶ Y) (tn : X ⟶ X) (ta : Y ⟶ Y)
    (hn : tn = 𝟙 X) (ha : ta = 𝟙 Y) (hp : p = q) :
    p ≫ ta = (B ◁ tn) ≫ q := by
  rw [ha, hn, whiskerLeft_id, Category.comp_id, Category.id_comp]
  exact hp

set_option maxHeartbeats 500000 in
-- The original free component proof unfolds both native evaluation comparisons.
/-- The actual native shifted cotensor module has the original full pair formula
under its existing complete target sequence comparison. -/
theorem native_target_pair_square (r : Operad.SmallFinBijGroupoid)
    (M : PointedCGWH.{u, v}) (N : OriginalModule.{u, v})
    (a n : Operad.SmallFinBijGroupoid) :
    FullFreeFunctionPair.targetAction (I := Operad.SmallFinBijGroupoid)
        (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N a n ≫
        (targetSequenceIso r M N).inv.natTrans.app (a ⊗ n) =
      (PointedCGWH.sphereSequenceCommMon.{u, v}.X.functor.obj a ◁ (targetSequenceIso r M N).inv.natTrans.app n) ≫
        FullFreeFunctionModuleComparison.pairAction (I := Operad.SmallFinBijGroupoid)
          (V := PointedCGWH.{u, v}) (A := PointedCGWH.sphereSequenceCommMon.{u, v})
          (reconstructedModule (target r M N)) a n := by
  let K := reconstructedModule (target r M N)
  let X := (ihom M).obj (N.X.functor.obj (n ⊗ r))
  let Y := (ihom M).obj (N.X.functor.obj ((a ⊗ n) ⊗ r))
  let p : PointedCGWH.sphereSequence.{u, v}.functor.obj a ⊗ X ⟶ Y :=
    FullFreeFunctionPair.targetAction (I := Operad.SmallFinBijGroupoid)
      (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N a n
  let q : PointedCGWH.sphereSequence.{u, v}.functor.obj a ⊗ X ⟶ Y :=
    FullFreeFunctionModuleComparison.pairAction (I := Operad.SmallFinBijGroupoid)
      (V := PointedCGWH.{u, v}) (A := PointedCGWH.sphereSequenceCommMon.{u, v}) K a n
  let tn : X ⟶ X := (targetSequenceIso r M N).inv.natTrans.app n
  let ta : Y ⟶ Y := (targetSequenceIso r M N).inv.natTrans.app (a ⊗ n)
  have hn : tn = 𝟙 X := targetSequenceIso_inv_component r M N n
  have ha : ta = 𝟙 Y := targetSequenceIso_inv_component r M N (a ⊗ n)
  have hq : q = p :=
    (reconstructedModule_pairAction (target r M N) a n).trans (target_pair r M N a n)
  exact identity_square (PointedCGWH.sphereSequence.{u, v}.functor.obj a) X Y p q tn ta hn ha hq.symm

set_option maxHeartbeats 1000000 in
-- The full native free comparison checks its complete module and enriched evaluation data.
/-- The original full free-unit/end maps and the independently proved actual
native target action give both inverse full module maps. -/
def moduleIso (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) (N : OriginalModule.{u, v}) :
    originalHom r M N ≅ reconstructedModule (target r M N) :=
  FullFreeFunctionTargetModule.comparison (I := Operad.SmallFinBijGroupoid)
    (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M N
    (reconstructedModule (target r M N)) (targetSequenceIso r M N).symm
    (by exact native_target_pair_square r M N)

/-- The actual original whole forward sequence map is retained. -/
theorem moduleIso_hom_sequence (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) (N : OriginalModule.{u, v}) :
    (moduleIso r M N).hom.hom = (sequenceIso r M N).hom := rfl

/-- The actual original whole inverse sequence map is retained. -/
theorem moduleIso_inv_sequence (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) (N : OriginalModule.{u, v}) :
    (moduleIso r M N).inv.hom = (sequenceIso r M N).inv := rfl

private theorem right_identity {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (e : Y ⟶ Y) (h : e = 𝟙 Y) : f ≫ e = f := by
  rw [h]
  exact Category.comp_id f

private theorem left_identity {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (e : X ⟶ X) (h : e = 𝟙 X) : e ≫ f = f := by
  rw [h]
  exact Category.id_comp f

/-- Every full forward native module component is the original beta map. -/
theorem moduleIso_hom_beta (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (moduleIso r M N).hom.hom.natTrans.app n = forwardLevel r M N n := by
  have h := congrArg (fun z => z.natTrans.app n) (moduleIso_hom_sequence r M N)
  exact h.trans (right_identity (forwardLevel r M N n)
    ((targetSequenceIso r M N).inv.natTrans.app n) (targetSequenceIso_inv_component r M N n))

/-- Every inverse native module component is the same original end extension. -/
theorem moduleIso_inv_beta (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v})
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (moduleIso r M N).inv.hom.natTrans.app n = inverseLevel r M N n := by
  have h := congrArg (fun z => z.natTrans.app n) (moduleIso_inv_sequence r M N)
  exact h.trans (left_identity (inverseLevel r M N n)
    ((targetSequenceIso r M N).hom.natTrans.app n) (targetSequenceIso_hom_component r M N n))


end NativeOmegaRecovery.NativeSymmetricFreeFunction
