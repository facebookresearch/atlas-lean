/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyQuillenEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSmithCSSReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.GammaZeroCoreComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.TrueSpacePowerConsumer
import MathlibExt.AlgebraicTopology.ModelCategory.Proper
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoReplacement
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The original complete onefold zero core and its quasicategory core

The first Joyal–Tierney right adjoint sends a genuine complete Segal space
to a fibrant Joyal object. Its original counit and the original Gamma unit
are glued by the native functor-category pushout. Gamma's unit is monic
through its original inner degeneracies, so both pushout injections are
Rezk weak by trivial-cofibration cobase change and native cofibrant
properness. The canonical original Smith CSS replacement sends this whole pushout to a
complete Segal space. Local Whitehead then gives a natural weak cospan
between the original zero space and the native equivalence-edge core.

The construction retains the actual units, counit, pushout injections and
replacement unit. Fibrancy and all weak-map hypotheses are proved from
completeness; no comparison map or outcome is supplied as a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.OnefoldCoreComparison

@[instance_reducible]
private def rezkModel : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
@[instance_reducible]
private def joyalModel : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory

attribute [local instance] rezkModel joyalModel

/-- The actual first JT right image retains the original inner-zero components. -/
def row : SimplicialSpace.{u} ⥤ SSet.{u} := comparisonRight ⋙ JoyalSSet.forget

/-- The actual first JT right object is fibrant for every complete Segal target. -/
theorem right_isFibrant (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    IsFibrant (comparisonRight.obj W) := by
  let _ : comparisonAdjunction.{u}.IsQuillenAdjunction := comparisonAdjunction_isQuillen
  exact (Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := comparisonAdjunction)).isFibrant
      ((RezkModel.isFibrant_iff_completeSegalSpaces W).mpr hW)

/-- The same original row is a quasicategory, without an extra derived-side hypothesis. -/
theorem row_isQuasicategory (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    SSet.Quasicategory (row.obj W) :=
  (JoyalSSet.isFibrant_iff_quasicategory (comparisonRight.obj W)).mp (right_isFibrant W hW)

/-- The original first left image of the original first right object. -/
abbrev firstImage : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  comparisonRight ⋙ comparisonLeft

/-- The original Gamma presentation of that same row, including every target map. -/
def gamma : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  row ⋙ SSet.Rezk.gammaDiagram ⋙ ofSimplicialObject

/-- The left leg before gluing is precisely the existing JT counit. -/
def counit : firstImage.{u} ⟶ 𝟭 SimplicialSpace.{u} := comparisonAdjunction.counit

/-- The right leg before gluing is precisely the existing Gamma unit. -/
def gammaUnit : firstImage.{u} ⟶ gamma.{u} where
  app W := ofSimplicialObject.map (SSet.Rezk.gammaUnit.app (row.obj W))
  naturality W V f := by
    change ofSimplicialObject.map
        (SSet.simplicialSpaceDiscrete.map (row.map f)) ≫
          ofSimplicialObject.map (SSet.Rezk.gammaUnit.app (row.obj V)) =
      ofSimplicialObject.map (SSet.Rezk.gammaUnit.app (row.obj W)) ≫
        ofSimplicialObject.map (SSet.Rezk.gammaDiagram.map (row.map f))
    rw [← ofSimplicialObject.map_comp, ← ofSimplicialObject.map_comp,
      SSet.Rezk.gammaUnit.naturality]

private theorem gammaUnit_component_mono (Q : SSet.{u}) (m n : SimplexCategoryᵒᵖ) :
    Mono (((SSet.Rezk.gammaUnit.app Q).app m).app n) := by
  let X := (SSet.Rezk.gammaDiagram.obj Q).obj m
  let d := SimplexCategory.const n.unop ⦋0⦌ 0
  let s := SimplexCategory.const ⦋0⦌ n.unop 0
  let g := X.map d.op
  let r := X.map s.op
  have hds : s ≫ d = 𝟙 ⦋0⦌ :=
    (SimplexCategory.eq_const_to_zero _).trans
      (SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm
  have hg : g ≫ r = 𝟙 (X.obj (op ⦋0⦌)) := by
    dsimp only [g, r]
    rw [← X.map_comp, ← op_comp, hds, op_id, X.map_id]
  let _ : IsSplitMono g := IsSplitMono.mk' ⟨r, hg⟩
  let _ : Mono g := inferInstance
  rw [SSet.Rezk.gammaUnit_app]
  change Mono ((SSet.Rezk.gammaZerothRowIso.inv.app Q).app m ≫ g)
  infer_instance

/-- Gamma's actual unit is monic by its original inner degeneracies. -/
theorem gammaUnit_mono (W : SimplicialSpace.{u}) : Mono (gammaUnit.app W) := by
  let _ : ∀ m : SimplexCategoryᵒᵖ,
      Mono ((SSet.Rezk.gammaUnit.app (row.obj W)).app m) := fun m => by
    let _ : ∀ n : SimplexCategoryᵒᵖ,
        Mono (((SSet.Rezk.gammaUnit.app (row.obj W)).app m).app n) :=
      fun n => gammaUnit_component_mono (row.obj W) m n
    exact NatTrans.mono_of_mono_app _
  let _ : Mono (SSet.Rezk.gammaUnit.app (row.obj W)) := NatTrans.mono_of_mono_app _
  exact ofSimplicialObject.map_mono _

/-- The Gamma unit is Rezk weak for the row proved fibrant by the actual JT adjunction. -/
theorem gammaUnit_rezkWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    rezkWeakEquivalences (gammaUnit.app W) := by
  let _ : SSet.Quasicategory (row.obj W) := row_isQuasicategory W hW
  exact (SSet.Rezk.gammaDiagram_replacement (row.obj W)).2.1

/-- The Gamma endpoint is complete for the same genuine row quasicategory. -/
theorem gamma_complete (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    completeSegalSpaces (gamma.obj W) := by
  let _ : SSet.Quasicategory (row.obj W) := row_isQuasicategory W hW
  exact (SSet.Rezk.gammaDiagram_replacement (row.obj W)).1

/-- The whole original counit and Gamma unit are glued by the native pushout functor. -/
def amalgam : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} := pushout counit gammaUnit

/-- The target injection is the first literal native pushout injection. -/
def fromTarget : 𝟭 SimplicialSpace.{u} ⟶ amalgam.{u} := pushout.inl counit gammaUnit

/-- The Gamma injection is the second literal native pushout injection. -/
def fromGamma : gamma.{u} ⟶ amalgam.{u} := pushout.inr counit gammaUnit

/-- The original counit and Gamma unit commute with the two actual injections. -/
theorem amalgam_square : counit.{u} ≫ fromTarget = gammaUnit ≫ fromGamma :=
  pushout.condition

private theorem amalgam_isPushout (W : SimplicialSpace.{u}) :
    IsPushout (counit.app W) (gammaUnit.app W) (fromTarget.app W) (fromGamma.app W) :=
  (IsPushout.of_hasPushout counit gammaUnit).map
    ((CategoryTheory.evaluation SimplicialSpace.{u} SimplicialSpace.{u}).obj W)

/-- The target injection is weak by actual trivial-cofibration cobase change. -/
theorem fromTarget_rezkWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    rezkWeakEquivalences (fromTarget.app W) := by
  have hγ : trivialCofibrations SimplicialSpace.{u} (gammaUnit.app W) := by
    rw [RezkModel.modelCategory_trivialCofibrations]
    exact ⟨gammaUnit_mono W, gammaUnit_rezkWeak W hW⟩
  have h := ((trivialCofibrations SimplicialSpace.{u}).of_isPushout
    (amalgam_isPushout W) hγ).2
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (fromTarget.app W) at h
  rwa [RezkModel.modelCategory_weakEquivalences] at h

/-- The Gamma injection is weak by the native cofibrant Rezk pushout theorem. -/
theorem fromGamma_rezkWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    rezkWeakEquivalences (fromGamma.app W) := by
  let _ : IsLeftProper SimplicialSpace.{u} :=
    isLeftProper_of_all_objects_cofibrant TrueSpacePowerPreparation.actualRezk_isCofibrant
  let _ : Cofibration (gammaUnit.app W) := by
    rw [cofibration_iff]
    change RezkModel.modelCategory.categoryWithCofibrations.cofibrations _
    rw [RezkModel.modelCategory_cofibrations]
    exact gammaUnit_mono W
  let _ : WeakEquivalence (counit.app W) := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _
    rw [RezkModel.modelCategory_weakEquivalences]
    exact comparisonAdjunction_counit_rezkWeak W hW
  have h := (IsLeftProper.weakEquivalence_of_isPushout
    (amalgam_isPushout W).flip).mem
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _ at h
  rwa [RezkModel.modelCategory_weakEquivalences] at h

/-- Replace the whole actual pushout, rather than either core or either original endpoint. -/
def common : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} := amalgam ⋙ OriginalSmithCSS.replacement

/-- The target leg retains its original injection followed by the canonical original Smith unit. -/
def targetLeg : 𝟭 SimplicialSpace.{u} ⟶ common.{u} :=
  fromTarget ≫ Functor.whiskerLeft amalgam OriginalSmithCSS.unit

/-- The Gamma leg retains its original injection followed by that same original Smith unit. -/
def gammaLeg : gamma.{u} ⟶ common.{u} :=
  fromGamma ≫ Functor.whiskerLeft amalgam OriginalSmithCSS.unit

/-- The target leg has exactly the original injection/unit composite at each original target. -/
theorem targetLeg_app (W : SimplicialSpace.{u}) :
    targetLeg.app W = fromTarget.app W ≫ OriginalSmithCSS.unit.app (amalgam.obj W) := rfl

/-- The Gamma leg uses exactly the same original replacement unit at its original pushout. -/
theorem gammaLeg_app (W : SimplicialSpace.{u}) :
    gammaLeg.app W = fromGamma.app W ≫ OriginalSmithCSS.unit.app (amalgam.obj W) := rfl

/-- The common endpoint is complete for every original input. -/
theorem common_complete (W : SimplicialSpace.{u}) : completeSegalSpaces (common.obj W) :=
  OriginalSmithCSS.replacement_completeSegal (amalgam.obj W)

/-- The whole target leg is Rezk weak at every genuine complete target. -/
theorem targetLeg_rezkWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    rezkWeakEquivalences (targetLeg.app W) := by
  rw [targetLeg_app]
  exact rezkWeakEquivalences.comp_mem (fromTarget.app W)
    (OriginalSmithCSS.unit.app (amalgam.obj W)) (fromTarget_rezkWeak W hW)
      (OriginalSmithCSS.unit_rezkWeak (amalgam.obj W))

/-- The whole Gamma leg is Rezk weak at the same complete target. -/
theorem gammaLeg_rezkWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    rezkWeakEquivalences (gammaLeg.app W) := by
  rw [gammaLeg_app]
  exact rezkWeakEquivalences.comp_mem (fromGamma.app W)
    (OriginalSmithCSS.unit.app (amalgam.obj W)) (fromGamma_rezkWeak W hW)
      (OriginalSmithCSS.unit_rezkWeak (amalgam.obj W))

/-- Evaluation is at the original outer zero object, retaining the whole inner simplicial set. -/
def zeroEvaluation : SimplicialSpace.{u} ⥤ SSet.{u} :=
  forget ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋0⦌)

/-- The common scalar object is the original zero space of the complete common presentation. -/
def commonCore : SimplicialSpace.{u} ⥤ SSet.{u} := common ⋙ zeroEvaluation

/-- The target's literal zero space maps to that common zero object. -/
def targetCoreLeg : zeroEvaluation.{u} ⟶ commonCore.{u} :=
  Functor.whiskerRight targetLeg zeroEvaluation

/-- The Gamma zero space maps through its original injection and replacement. -/
def gammaCoreLeg : gamma.{u} ⋙ zeroEvaluation.{u} ⟶ commonCore.{u} :=
  Functor.whiskerRight gammaLeg zeroEvaluation

/-- The original quasicategory's native equivalence-edge core functor. -/
def nativeCore : SimplicialSpace.{u} ⥤ SSet.{u} := row ⋙ SSet.coreFunctor

/-- Use the frozen raw Gamma-zero comparison on the actual first right image. -/
def gammaCoreIso : gamma.{u} ⋙ zeroEvaluation.{u} ≅ nativeCore.{u} :=
  NatIso.ofComponents (fun W => SSet.Rezk.gammaZeroCoreIso (row.obj W))
    (fun f => SSet.Rezk.gammaZeroCoreIso_natural (row.map f))

/-- The native core leg uses the original Gamma presentation inverse and its actual common leg. -/
def nativeCoreLeg : nativeCore.{u} ⟶ commonCore.{u} := gammaCoreIso.inv ≫ gammaCoreLeg

private theorem zero_weak_of_rezkWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hf : rezkWeakEquivalences f) :
    SSet.realizationWeakEquivalences (zeroEvaluation.map f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact ((ReedyModel.weakEquivalence_iff f).mp
    ((rezkWeak_iff_reedyWeak_of_completeSegalSpaces f hW hV).mp hf)) 0

/-- The actual target-core leg is scalar weak by complete-endpoint local Whitehead. -/
theorem targetCoreLeg_weak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    SSet.realizationWeakEquivalences (targetCoreLeg.app W) := by
  change SSet.realizationWeakEquivalences (zeroEvaluation.map (targetLeg.app W))
  exact zero_weak_of_rezkWeak (targetLeg.app W) hW (common_complete W)
    (targetLeg_rezkWeak W hW)

/-- The Gamma zero leg is weak through the actual complete Gamma and common endpoints. -/
theorem gammaCoreLeg_weak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    SSet.realizationWeakEquivalences (gammaCoreLeg.app W) := by
  change SSet.realizationWeakEquivalences (zeroEvaluation.map (gammaLeg.app W))
  exact zero_weak_of_rezkWeak (gammaLeg.app W) (gamma_complete W hW) (common_complete W)
    (gammaLeg_rezkWeak W hW)

/-- The actual native-core leg is scalar weak through the same complete common endpoint. -/
theorem nativeCoreLeg_weak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    SSet.realizationWeakEquivalences (nativeCoreLeg.app W) := by
  change SSet.realizationWeakEquivalences (gammaCoreIso.inv.app W ≫ gammaCoreLeg.app W)
  exact SSet.realizationWeakEquivalences.comp_mem
    (gammaCoreIso.inv.app W) (gammaCoreLeg.app W)
    (SSet.realizationWeakEquivalences.of_isIso (gammaCoreIso.inv.app W))
    (gammaCoreLeg_weak W hW)

/-- The native core is Kan for the row whose quasicategory structure was proved from completeness. -/
theorem nativeCore_isKan (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    SSet.KanComplex (nativeCore.obj W) := by
  let _ : SSet.Quasicategory (row.obj W) := row_isQuasicategory W hW
  exact SSet.kanComplex_core_of_quasicategory (row.obj W)


/-- The original counit/unit square is retained after the same actual replacement unit. -/
theorem common_square : counit.{u} ≫ targetLeg = gammaUnit ≫ gammaLeg := by
  let e : amalgam.{u} ⟶ common.{u} := Functor.whiskerLeft amalgam OriginalSmithCSS.unit
  exact (Category.assoc counit fromTarget e).symm.trans
    ((congrArg (fun p : firstImage.{u} ⟶ amalgam.{u} => p ≫ e) amalgam_square).trans
      (Category.assoc gammaUnit fromGamma e))

/-- Evaluating the original whole square retains both original zero maps. -/
theorem core_square (W : SimplicialSpace.{u}) :
    zeroEvaluation.map (counit.app W) ≫ targetCoreLeg.app W =
      zeroEvaluation.map (gammaUnit.app W) ≫ gammaCoreLeg.app W := by
  have h : counit.app W ≫ targetLeg.app W = gammaUnit.app W ≫ gammaLeg.app W :=
    congr_app common_square W
  exact (zeroEvaluation.map_comp (counit.app W) (targetLeg.app W)).symm.trans
    ((congrArg zeroEvaluation.map h).trans
      (zeroEvaluation.map_comp (gammaUnit.app W) (gammaLeg.app W)))

/-- Both scalar legs send each original zero vertex to precisely the same common vertex. -/
theorem original_vertex_square (W : SimplicialSpace.{u})
    (x : (zeroEvaluation.obj W) _⦋0⦌) :
    (targetCoreLeg.app W).app (op ⦋0⦌) x =
      (nativeCoreLeg.app W).app (op ⦋0⦌)
        ⟨x, SSet.mem_core_obj_zero (X := row.obj W) x⟩ := by
  let y := (zeroEvaluation.map (gammaUnit.app W)).app (op ⦋0⦌) x
  let p : (nativeCore.obj W) _⦋0⦌ :=
    ⟨x, SSet.mem_core_obj_zero (X := row.obj W) x⟩
  let e := ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)).mapIso
    (gammaCoreIso.app W)
  have hy : e.hom y = p := by
    apply Subtype.ext
    exact SSet.Rezk.gammaZeroCoreIso_unit_vertex (row.obj W) x
  have hinv : e.inv p = y := by
    apply e.toEquiv.injective
    exact (e.toEquiv.apply_symm_apply p).trans hy.symm
  have hc : (zeroEvaluation.map (counit.app W)).app (op ⦋0⦌) x = x := by
    change (((comparisonAdjunction.counit.app W).hom.app (op ⦋0⦌)).app (op ⦋0⦌)) x = x
    rw [comparisonAdjunction_counit_app]
    have h0 : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ :=
      (SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm
    rw [h0, op_id]
    exact ConcreteCategory.congr_hom
      ((W.diagram.obj (op ⦋0⦌)).map_id (op ⦋0⦌)) x
  have hs := ConcreteCategory.congr_hom (congr_app (core_square W) (op ⦋0⦌)) x
  change (targetCoreLeg.app W).app (op ⦋0⦌)
    ((zeroEvaluation.map (counit.app W)).app (op ⦋0⦌) x) =
      (gammaCoreLeg.app W).app (op ⦋0⦌) y at hs
  have hp : (targetCoreLeg.app W).app (op ⦋0⦌) x =
      (gammaCoreLeg.app W).app (op ⦋0⦌) y :=
    (congrArg ((targetCoreLeg.app W).app (op ⦋0⦌)) hc).symm.trans hs
  have hn : (nativeCoreLeg.app W).app (op ⦋0⦌) p =
      (gammaCoreLeg.app W).app (op ⦋0⦌) (e.inv p) := rfl
  exact hp.trans ((congrArg ((gammaCoreLeg.app W).app (op ⦋0⦌)) hinv).symm.trans hn.symm)

/-- The actual complete targets, retaining their original simplicial spaces and maps. -/
abbrev CompleteTargets := completeSegalSpaces.{u}.FullSubcategory

/-- The scalar Ho values of the original complete-target zero spaces. -/
def targetHo := completeSegalSpaces.{u}.ι ⋙ zeroEvaluation.{u} ⋙ SSet.realizationWeakEquivalences.Q

/-- The scalar Ho values of their actual first-right-image native cores. -/
def nativeHo := completeSegalSpaces.{u}.ι ⋙ nativeCore.{u} ⋙ SSet.realizationWeakEquivalences.Q

/-- The scalar Ho values of the same original complete common presentations. -/
def commonHo := completeSegalSpaces.{u}.ι ⋙ commonCore.{u} ⋙ SSet.realizationWeakEquivalences.Q

/-- Localize the actual target leg; no other representative is selected. -/
def targetHoLeg : targetHo.{u} ⟶ commonHo.{u} :=
  Functor.whiskerRight (Functor.whiskerLeft completeSegalSpaces.ι targetCoreLeg)
    SSet.realizationWeakEquivalences.Q

/-- Localize the actual native-core leg of the same weak cospan. -/
def nativeHoLeg : nativeHo.{u} ⟶ commonHo.{u} :=
  Functor.whiskerRight (Functor.whiskerLeft completeSegalSpaces.ι nativeCoreLeg)
    SSet.realizationWeakEquivalences.Q

/-- The target leg is inverted only by its proved native scalar weakness. -/
theorem targetHoLeg_isIso : IsIso targetHoLeg.{u} := by
  have h : ∀ W : CompleteTargets.{u}, IsIso (targetHoLeg.app W) := by
    intro W
    change IsIso (SSet.realizationWeakEquivalences.Q.map (targetCoreLeg.app W.obj))
    exact Localization.inverts SSet.realizationWeakEquivalences.Q SSet.realizationWeakEquivalences
      _ (targetCoreLeg_weak W.obj W.property)
  exact NatIso.isIso_of_isIso_app _

/-- The native-core leg is inverted by the same complete-endpoint scalar argument. -/
theorem nativeHoLeg_isIso : IsIso nativeHoLeg.{u} := by
  have h : ∀ W : CompleteTargets.{u}, IsIso (nativeHoLeg.app W) := by
    intro W
    change IsIso (SSet.realizationWeakEquivalences.Q.map (nativeCoreLeg.app W.obj))
    exact Localization.inverts SSet.realizationWeakEquivalences.Q SSet.realizationWeakEquivalences
      _ (nativeCoreLeg_weak W.obj W.property)
  exact NatIso.isIso_of_isIso_app _

/-- The genuine onefold core comparison is the natural Ho Iso induced by those two actual weak legs. -/
def coreHoIso : targetHo.{u} ≅ nativeHo.{u} := by
  let _ : IsIso targetHoLeg.{u} := targetHoLeg_isIso
  let _ : IsIso nativeHoLeg.{u} := nativeHoLeg_isIso
  exact asIso targetHoLeg ≪≫ (asIso nativeHoLeg).symm

/-- The characteristic Ho triangle retains both literal localized weak legs. -/
theorem coreHoIso_triangle : coreHoIso.{u}.hom ≫ nativeHoLeg = targetHoLeg := by
  let _ : IsIso targetHoLeg.{u} := targetHoLeg_isIso
  let _ : IsIso nativeHoLeg.{u} := nativeHoLeg_isIso
  change ((asIso targetHoLeg).hom ≫ (asIso nativeHoLeg).inv) ≫ (asIso nativeHoLeg).hom =
    (asIso targetHoLeg).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every original map of complete targets acts through the same natural core comparison. -/
theorem coreHoIso_natural {W V : CompleteTargets.{u}} (f : W ⟶ V) :
    targetHo.map f ≫ coreHoIso.hom.app V = coreHoIso.hom.app W ≫ nativeHo.map f :=
  coreHoIso.hom.naturality f

end SimplicialSpace.OnefoldCoreComparison
