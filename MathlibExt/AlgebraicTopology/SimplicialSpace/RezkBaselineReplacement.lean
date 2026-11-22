/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Fixed unlocalized baseline; no caller model or factorization outcome.
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanModel
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.TrueSpacePowerConsumer
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Functorial baseline replacement of simplicial spaces

Transporting the injective Kan terminal-map factorization defines a functorial replacement of
simplicial spaces. Its unit is a levelwise monomorphism and realization weak equivalence, hence
a trivial cofibration in the named Reedy model, and every replacement target is Reedy fibrant.
-/

public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
    HomotopicalAlgebra Opposite
open scoped Simplicial
namespace SimplicialSpace.RezkBaselineReplacement

private abbrev rawToSpace : (SimplicialPresheaf.{u} SimplexCategory) ≌ SimplicialSpace.{u} :=
  SimplicialSpace.equivalenceSimplicialObject.symm

private def factorization : FunctorialFactorizationData
    ((SimplicialPresheaf.InjectiveKan.trivialMonomorphisms.{u} SimplexCategory).inverseImage
      SimplicialSpace.forget)
    ((SimplicialPresheaf.InjectiveKan.injectiveFibrations.{u} SimplexCategory).inverseImage
      SimplicialSpace.forget) := by
  letI :
      (SimplicialPresheaf.InjectiveKan.trivialMonomorphisms.{u} SimplexCategory).RespectsIso := by
    unfold SimplicialPresheaf.InjectiveKan.trivialMonomorphisms
      SimplicialPresheaf.objectwiseKanWeakEquivalences
    infer_instance
  letI : (SimplicialPresheaf.InjectiveKan.injectiveFibrations.{u} SimplexCategory).RespectsIso := by
    unfold SimplicialPresheaf.InjectiveKan.injectiveFibrations
    infer_instance
  exact
      (SimplicialPresheaf.InjectiveKan.data.{u}
        SimplexCategory).trivialCofibrationFactorization.ofEquivalence
    rawToSpace.symm

private def terminalArrow : SimplicialSpace.{u} ⥤ Arrow SimplicialSpace.{u} where
  obj W := Arrow.mk (terminal.from W)
  map f := Arrow.homMk f (𝟙 _) (by simp)
  map_id W := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- The functorial midpoint comes from the SAME native factorization of the actual terminal map. -/
def replacement : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  terminalArrow ⋙ factorization.Z

/-- The original source arrow, including the actual carrier unit of equivalence transport. -/
def unit : 𝟭 SimplicialSpace.{u} ⟶ replacement where
  app W := factorization.i.app (terminalArrow.obj W)
  naturality W V f := factorization.i.naturality (terminalArrow.map (f : W ⟶ V))

/-- Every original map is preserved by the actual functorial replacement unit. -/
theorem unit_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f ≫ unit.app V = unit.app W ≫ replacement.map f :=
  unit.naturality f

/-- The SAME named unlocalized Reedy model sees the actual unit as a trivial cofibration. -/
theorem unit_trivialCofibration (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    Cofibration (unit.app W) ∧ WeakEquivalence (unit.app W) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  have h := factorization.hi (terminalArrow.obj W)
  change (Mono (SimplicialSpace.forget.map (unit.app W)) ∧
    ∀ n : SimplexCategoryᵒᵖ,
      SSet.realizationWeakEquivalences ((SimplicialSpace.forget.map (unit.app W)).app n)) at h
  exact ⟨(SimplicialSpace.ReedyModel.cofibration_iff _).mpr
      ((SimplicialSpace.mono_forget_map_iff _).mp h.1),
    (SimplicialSpace.ReedyModel.weakEquivalence_iff _).mpr (fun n => h.2 (op ⦋n⦌))⟩

/-- ALL actual components, including degree zero, are mono and realization weak. -/
theorem unit_components (W : SimplicialSpace.{u}) (n : ℕ) :
    Mono ((unit.app W).hom.app (op ⦋n⦌)) ∧
      SSet.realizationWeakEquivalences ((unit.app W).hom.app (op ⦋n⦌)) := by
  have h := factorization.hi (terminalArrow.obj W)
  change (Mono (SimplicialSpace.forget.map (unit.app W)) ∧
    ∀ a : SimplexCategoryᵒᵖ,
      SSet.realizationWeakEquivalences ((SimplicialSpace.forget.map (unit.app W)).app a)) at h
  exact ⟨(NatTrans.mono_iff_mono_app (SimplicialSpace.forget.map (unit.app W))).mp h.1
      (op ⦋n⦌), h.2 (op ⦋n⦌)⟩

/-- Actual GLOBAL right lifting to the preserved terminal image gives named Reedy fibrancy. -/
theorem replacement_fibrant (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    IsFibrant (replacement.obj W) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
    (SimplicialPresheaf.InjectiveKan.data.{u} SimplexCategory).model
  let p := factorization.p.app (terminalArrow.obj W)
  have hp := factorization.hp (terminalArrow.obj W)
  change SimplicialPresheaf.InjectiveKan.injectiveFibrations SimplexCategory
    (SimplicialSpace.forget.map p) at hp
  have hFib : Fibration (SimplicialSpace.forget.map p) := by
    rw [HomotopicalAlgebra.fibration_iff]
    change
        (SimplicialPresheaf.InjectiveKan.data.{u}
          SimplexCategory).model.categoryWithFibrations.fibrations
      (SimplicialSpace.forget.map p)
    rw [(SimplicialPresheaf.InjectiveKan.data.{u} SimplexCategory).fibrations_eq]
    exact hp
  have ht : IsTerminal (SimplicialSpace.forget.obj (⊤_ SimplicialSpace.{u})) :=
    (terminalIsTerminal (C := SimplicialSpace.{u})).isTerminalObj SimplicialSpace.forget _
  have hRaw : IsFibrant (SimplicialSpace.forget.obj (replacement.obj W)) :=
    (HomotopicalAlgebra.isFibrant_iff_of_isTerminal (SimplicialSpace.forget.map p) ht).mpr hFib
  change IsFibrant (SimplicialSpace.ofSimplicialObject.obj
    (SimplicialSpace.forget.obj (replacement.obj W)))
  exact (TrueSpacePowerPreparation.baselineFibrant_iff
    (SimplicialSpace.forget.obj (replacement.obj W))).mp hRaw

end SimplicialSpace.RezkBaselineReplacement
