/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.AllCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSpace.BoxProduct
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkRowFibrations
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The actual Joyal–Tierney Quillen adjunction

The original left functor preserves the native monomorphism cofibrations.
The canonical genuine row theorem at the original empty-to-point map
identifies the actual right image as a Joyal fibration. Native JT7.15 and
Brown give the Quillen class and all-arrow left weak preservation, for the
actual chosen Joyal and Rezk models.

Source: JT4.11, printed page 25; Quillen proof via JT4.3 and JT7.15.
-/

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MorphismProperty Opposite
open HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner


namespace SimplicialSpace

private lemma comparisonLeft_mono {A B : JoyalSSet.{u}} (f : A ⟶ B) [Mono f] :
    Mono (SimplicialSpace.comparisonLeft.map f) := by
  let _ : Mono (JoyalSSet.forget.map f) := inferInstance
  have hcomponents : ∀ m, Mono ((JoyalSSet.forget.map f).app m) :=
    (NatTrans.mono_iff_mono_app (JoyalSSet.forget.map f)).mp inferInstance
  let _ : ∀ m, Mono ((SimplicialSpace.comparisonLeft.map f).hom.app m) := fun m => by
    let _ : ∀ n, Mono (((SimplicialSpace.comparisonLeft.map f).hom.app m).app n) :=
      fun n => by
        rw [SimplicialSpace.comparisonLeft_map_app]
        exact hcomponents m
    exact NatTrans.mono_of_mono_app _
  apply SimplicialSpace.forget.mono_of_mono_map
  exact NatTrans.mono_of_mono_app _

/-- Actual selected-model cofibrations are preserved by the literal first projection. -/
private lemma comparisonLeft_preservesCofibrations :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
    PreservesCofibrations SimplicialSpace.comparisonLeft := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
  intro A B f hf
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations f at hf
  rw [JoyalSSet.modelCategory_cofibrations] at hf
  let _ : Mono f := hf
  change SimplicialSpace.RezkModel.modelCategory.categoryWithCofibrations.cofibrations
    (SimplicialSpace.comparisonLeft.map f)
  rw [SimplicialSpace.RezkModel.modelCategory_cofibrations]
  exact comparisonLeft_mono f

private def boxEmptyIsInitial (A : SSet.{u}) :
    IsInitial ((SimplicialSpace.boxProduct.obj A).obj (⊥_ SSet.{u})) := by
  let _ : (SimplicialSpace.boxProduct.obj A).IsLeftAdjoint :=
    (SimplicialSpace.boxProductLeftAdjunction₂.adj A).isLeftAdjoint
  exact (initialIsInitial : IsInitial (⊥_ SSet.{u})).isInitialObj
    (SimplicialSpace.boxProduct.obj A) _

/-- The actual power by the empty scalar is terminal, without any model hypothesis. -/
private def rowPowerEmptyIsTerminal (X : SimplicialSpace.{u}) :
    IsTerminal ((SimplicialSpace.rowPowerFunctor (⊥_ SSet.{u})).obj X) := by
  let e (A : SSet.{u}) :
      (((SimplicialSpace.boxProduct.obj A).obj (⊥_ SSet.{u})) ⟶ X) ≃
        (A ⟶ (SimplicialSpace.rowPowerFunctor (⊥_ SSet.{u})).obj X) :=
    (SimplicialSpace.boxProductRightAdjunction (⊥_ SSet.{u})).homEquiv A X
  refine IsTerminal.ofUniqueHom (fun A => e A ((boxEmptyIsInitial A).to X)) ?_
  intro A f
  apply (e A).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (boxEmptyIsInitial A).hom_ext ((e A).symm f) ((boxEmptyIsInitial A).to X)

private def rowZeroPowerIso (X : SimplicialSpace.{u}) :
    (SimplicialSpace.rowPowerFunctor (Δ[0] : SSet.{u})).obj X ≅
      JoyalSSet.forget.obj (SimplicialSpace.comparisonRight.obj X) :=
  SimplicialSpace.rowRepresentableIso 0 X

private lemma rowZeroPower_naturality {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    (SimplicialSpace.rowPowerFunctor (Δ[0] : SSet.{u})).map p ≫
        (rowZeroPowerIso Y).hom =
      (rowZeroPowerIso X).hom ≫
        (JoyalSSet.forget.map (SimplicialSpace.comparisonRight.map p)) := by
  exact SSet.Rezk.pointwiseYonedaIso_naturality_target 0
    (SimplicialSpace.HorizontalModel.transposeSpaceEquivalence.functor.map p).hom

/-- The whole original empty-to-point row pullback-Hom is the actual zeroth-row map. -/
private def rowZeroPullbackArrowIso {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    Arrow.mk (SimplicialSpace.rowPullbackHom
      (initial.to (Δ[0] : SSet.{u})) p) ≅
      Arrow.mk (JoyalSSet.forget.map (SimplicialSpace.comparisonRight.map p)) := by
  let v := initial.to (Δ[0] : SSet.{u})
  let sq := SimplicialSpace.rowPullbackHomSquare v p
  let _ : IsIso ((SimplicialSpace.innerHomFunctor.obj
      (op (SimplicialSpace.discreteInner (⊥_ SSet.{u})))).map
        (SimplicialSpace.HorizontalModel.transposeSpaceEquivalence.functor.map p)) :=
    isIso_of_isTerminal (rowPowerEmptyIsTerminal X) (rowPowerEmptyIsTerminal Y) _
  let _ : IsIso sq.snd := sq.isPullback.isIso_snd_of_isIso
  exact Arrow.isoMk' (SimplicialSpace.rowPullbackHom v p)
    (JoyalSSet.forget.map (SimplicialSpace.comparisonRight.map p))
    (rowZeroPowerIso X)
    (asIso sq.snd ≪≫ rowZeroPowerIso Y) (by
      rw [Iso.trans_hom, asIso_hom, ← Category.assoc,
        SimplicialSpace.rowPullbackHom_snd]
      exact (rowZeroPower_naturality p).symm)

/-- Canonical genuine row lifting preserves the actual right fibrations between fibrant objects. -/
private lemma comparisonRight_preservesFibrationsBetweenFibrantObjects :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
    PreservesFibrationsBetweenFibrantObjects SimplicialSpace.comparisonRight := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
  intro X Y p hp
  have hX := (SimplicialSpace.RezkModel.isFibrant_iff_completeSegalSpaces X).mp hp.2.1
  have hY := (SimplicialSpace.RezkModel.isFibrant_iff_completeSegalSpaces Y).mp hp.2.2
  have hpR := hp.1
  change SimplicialSpace.RezkModel.modelCategory.categoryWithFibrations.fibrations p at hpR
  have hQ : SSet.categoricalFibrations (SimplicialSpace.rowPullbackHom
      (initial.to (Δ[0] : SSet.{u})) p) :=
    hasCategoricalRowPullbackHom_of_rezkFibration p hX hY hpR _ _ _ (by infer_instance)
  have hR : SSet.categoricalFibrations
      (JoyalSSet.forget.map (SimplicialSpace.comparisonRight.map p)) :=
    (SSet.categoricalFibrations.arrow_mk_iso_iff (rowZeroPullbackArrowIso p)).mp hQ
  change JoyalSSet.modelCategory.categoryWithFibrations.fibrations
    (SimplicialSpace.comparisonRight.map p)
  rw [JoyalSSet.modelCategory_fibrations]
  exact hR

/-- The original comparison adjunction is Quillen for the actual chosen MJ and MR. -/
theorem comparisonAdjunction_isQuillen :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
    Adjunction.IsQuillenAdjunction SimplicialSpace.comparisonAdjunction := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects
    comparisonLeft_preservesCofibrations
    comparisonRight_preservesFibrationsBetweenFibrantObjects

/-- Every original categorical weak arrow is preserved by the actual left functor. -/
theorem comparisonLeft_rezkWeak_of_categoricalEquivalence
    {A B : JoyalSSet.{u}} (f : A ⟶ B)
    (hf : SSet.categoricalEquivalences (JoyalSSet.forget.map f)) :
    SimplicialSpace.rezkWeakEquivalences (SimplicialSpace.comparisonLeft.map f) := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
  have hfW : weakEquivalences JoyalSSet.{u} f := by
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f
    rw [JoyalSSet.modelCategory_weakEquivalences]
    exact hf
  have hW :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_allObjectsCofibrant_of_fibrantCriterion
    SimplicialSpace.comparisonAdjunction comparisonLeft_preservesCofibrations
    comparisonRight_preservesFibrationsBetweenFibrantObjects
    JoyalSSet.isCofibrant f hfW
  change SimplicialSpace.RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (SimplicialSpace.comparisonLeft.map f) at hW
  simpa only [SimplicialSpace.RezkModel.modelCategory_weakEquivalences] using hW

end SimplicialSpace
