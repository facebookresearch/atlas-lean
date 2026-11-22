/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Cartesian compatibility of the named Reedy model

The Cartesian product and closed structure on designated simplicial spaces
are transported from their actual presheaf diagrams. The selected Reedy
model is kept explicit throughout.
-/

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open HomotopicalAlgebra
open scoped MonoidalCategory Simplicial

namespace SimplicialSpace.Cartesian

/-- Transport the actual presheaf Cartesian structure to the designated carrier. -/
scoped instance cartesianMonoidalCategory : CartesianMonoidalCategory SimplicialSpace.{u} where
  toMonoidalCategory := Monoidal.transport equivalenceSimplicialObject.{u}.symm
  isTerminalTensorUnit :=
    CartesianMonoidalCategory.isTerminalTensorUnit.isTerminalObj ofSimplicialObject.{u} _
  fst X Y := ofSimplicialObject.map (CartesianMonoidalCategory.fst X.diagram Y.diagram)
  snd X Y := ofSimplicialObject.map (CartesianMonoidalCategory.snd X.diagram Y.diagram)
  tensorProductIsBinaryProduct X Y := by
    apply isLimitOfReflectsOfMapIsLimit forget
    exact CartesianMonoidalCategory.tensorProductIsBinaryProduct X.diagram Y.diagram
  fst_def X Y := by
    apply InducedCategory.hom_ext
    exact CartesianMonoidalCategory.fst_def X.diagram Y.diagram
  snd_def X Y := by
    apply InducedCategory.hom_ext
    exact CartesianMonoidalCategory.snd_def X.diagram Y.diagram

open scoped SimplicialSpace.Cartesian

/-- The symmetry is the original presheaf product swap. -/
scoped instance braidedCategory : BraidedCategory SimplicialSpace.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- Transport the genuine presheaf exponential, formed from the native Under ends. -/
scoped instance monoidalClosed : MonoidalClosed SimplicialSpace.{u} := by
  letI : EnrichedCategory SSet.{u} SSet.{u} := MonoidalClosed.enrichedCategorySelf _
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf _
  letI : MonoidalClosed (SimplicialObject SSet.{u}) :=
    MonoidalClosed.FunctorCategory.monoidalClosed
  letI : forget.{u}.Monoidal := Functor.Monoidal.ofChosenFiniteProducts forget
  exact MonoidalClosed.ofEquiv forget equivalenceSimplicialObject.toAdjunction

end SimplicialSpace.Cartesian

open scoped SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.ReedyModel

private abbrev eval (n : ℕ) : SimplicialSpace.{u} ⥤ SSet.{u} :=
  forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (Opposite.op ⦋n⦌)

private def evaluatedPushout
    {A B K L : SimplicialSpace.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) (n : ℕ) :
    (curriedTensor SSet.{u}).PushoutObjObj ((eval n).map i) ((eval n).map j) where
  pt := (eval n).obj sq.pt
  inl := (eval n).map sq.inl
  inr := (eval n).map sq.inr
  isPushout := sq.isPushout.map (eval n)
  ι := (eval n).map sq.ι
  inl_ι := by
    change (eval n).map sq.inl ≫ (eval n).map sq.ι =
      (eval n).map ((curriedTensor SimplicialSpace.{u}).obj B |>.map j)
    exact ((eval n).map_comp sq.inl sq.ι).symm.trans
      (congrArg (fun f => (eval n).map f) sq.inl_ι)
  inr_ι := by
    change (eval n).map sq.inr ≫ (eval n).map sq.ι =
      (eval n).map (((curriedTensor SimplicialSpace.{u}).map i).app L)
    exact ((eval n).map_comp sq.inr sq.ι).symm.trans
      (congrArg (fun f => (eval n).map f) sq.inr_ι)

private def evaluatedPushoutIso
    {A B K L : SimplicialSpace.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) (n : ℕ) :
    Arrow.mk ((eval n).map sq.ι) ≅
      (Arrow.mk ((eval n).map i) □ Arrow.mk ((eval n).map j)) := by
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    ((eval n).map i) ((eval n).map j)
  change Arrow.mk (evaluatedPushout i j sq n).ι ≅ Arrow.mk sq₀.ι
  exact Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SSet.{u})
    (f₁ := Arrow.mk ((eval n).map i)) (f₁' := Arrow.mk ((eval n).map i))
    (f₂ := Arrow.mk ((eval n).map j)) (evaluatedPushout i j sq n) sq₀
    (Iso.refl (Arrow.mk ((eval n).map i)))

private theorem cofibration_iff_eval {A B : SimplicialSpace.{u}} (i : A ⟶ B) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i ↔
      ∀ n, cofibrations SSet.{u} ((eval n).map i) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [← HomotopicalAlgebra.cofibration_iff, SimplicialSpace.ReedyModel.cofibration_iff]
  constructor
  · intro hi n
    let _ : Mono i := hi
    let _ : Mono ((eval n).map i) := inferInstance
    exact (HomotopicalAlgebra.cofibration_iff _).1
      (SSet.modelCategoryQuillen.cofibration_of_mono _)
  · intro h
    apply (mono_forget_map_iff i).mp
    apply (NatTrans.mono_iff_mono_app (forget.map i)).2
    intro n
    have hn := h n.unop.len
    let _ : Cofibration ((eval n.unop.len).map i) :=
      (HomotopicalAlgebra.cofibration_iff _).2 hn
    change Mono ((eval n.unop.len).map i)
    exact SSet.modelCategoryQuillen.mono_of_cofibration ((eval n.unop.len).map i)

private theorem weakEquivalence_iff_eval {A B : SimplicialSpace.{u}} (i : A ⟶ B) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    weakEquivalences SimplicialSpace.{u} i ↔
      ∀ n, weakEquivalences SSet.{u} ((eval n).map i) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [← HomotopicalAlgebra.weakEquivalence_iff]
  exact SimplicialSpace.ReedyModel.weakEquivalence_iff i

/-- The original supplied Cartesian pushout-product of Reedy cofibrations is a cofibration. -/
theorem cartesian_pushoutObjObj_cofibration
    {A B K L : SimplicialSpace.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i → cofibrations SimplicialSpace.{u} j →
      cofibrations SimplicialSpace.{u} sq.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi hj
  apply (cofibration_iff_eval sq.ι).2
  intro n
  let _ : Cofibration ((eval n).map i) :=
    (HomotopicalAlgebra.cofibration_iff _).2 ((cofibration_iff_eval i).1 hi n)
  let _ : Cofibration ((eval n).map j) :=
    (HomotopicalAlgebra.cofibration_iff _).2 ((cofibration_iff_eval j).1 hj n)
  apply ((cofibrations SSet.{u}).arrow_mk_iso_iff (evaluatedPushoutIso i j sq n)).2
  exact (HomotopicalAlgebra.cofibration_iff _).1 (SSet.cofibration_pushoutProduct _ _)

/-- The same supplied Cartesian pushout-product is trivial when the original left map is weak. -/
theorem cartesian_pushoutObjObj_trivial_of_left
    {A B K L : SimplicialSpace.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i → cofibrations SimplicialSpace.{u} j →
      weakEquivalences SimplicialSpace.{u} i →
        trivialCofibrations SimplicialSpace.{u} sq.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi hj hw
  refine ⟨cartesian_pushoutObjObj_cofibration i j sq hi hj, ?_⟩
  apply (weakEquivalence_iff_eval sq.ι).2
  intro n
  let _ : Cofibration ((eval n).map i) :=
    (HomotopicalAlgebra.cofibration_iff _).2 ((cofibration_iff_eval i).1 hi n)
  let _ : Cofibration ((eval n).map j) :=
    (HomotopicalAlgebra.cofibration_iff _).2 ((cofibration_iff_eval j).1 hj n)
  let _ : WeakEquivalence ((eval n).map i) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).2 ((weakEquivalence_iff_eval i).1 hw n)
  apply ((weakEquivalences SSet.{u}).arrow_mk_iso_iff (evaluatedPushoutIso i j sq n)).2
  exact (SSet.pushoutProduct_mem_trivialCofibrations_of_left _ _).2

/-- The same supplied Cartesian pushout-product is trivial when the original right map is weak. -/
theorem cartesian_pushoutObjObj_trivial_of_right
    {A B K L : SimplicialSpace.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i → cofibrations SimplicialSpace.{u} j →
      weakEquivalences SimplicialSpace.{u} j →
        trivialCofibrations SimplicialSpace.{u} sq.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi hj hw
  refine ⟨cartesian_pushoutObjObj_cofibration i j sq hi hj, ?_⟩
  apply (weakEquivalence_iff_eval sq.ι).2
  intro n
  let _ : Cofibration ((eval n).map i) :=
    (HomotopicalAlgebra.cofibration_iff _).2 ((cofibration_iff_eval i).1 hi n)
  let _ : Cofibration ((eval n).map j) :=
    (HomotopicalAlgebra.cofibration_iff _).2 ((cofibration_iff_eval j).1 hj n)
  let _ : WeakEquivalence ((eval n).map j) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).2 ((weakEquivalence_iff_eval j).1 hw n)
  apply ((weakEquivalences SSet.{u}).arrow_mk_iso_iff (evaluatedPushoutIso i j sq n)).2
  exact (SSet.pushoutProduct_mem_trivialCofibrations_of_right _ _).2

private theorem pushoutProduct_axiom :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    CartesianPushoutProductAxiom (C := SimplicialSpace.{u}) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  refine ⟨?_, ?_, ?_⟩
  · intro A B K L i j hi hj
    exact cartesian_pushoutObjObj_cofibration i j
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u}) i j) hi hj
  · intro A B K L i j hi hj
    exact cartesian_pushoutObjObj_trivial_of_left i j
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u}) i j) hi.1 hj hi.2
  · intro A B K L i j hi hj
    exact cartesian_pushoutObjObj_trivial_of_right i j
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u}) i j) hi hj.1 hj.2

private theorem pullbackHom_axiom :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    CartesianPullbackHomAxiom (C := SimplicialSpace.{u}) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  exact cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp pushoutProduct_axiom

private def pullbackObjObjIso
    {A B X Y : SimplicialSpace.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    Arrow.mk sq.π ≅ ((Opposite.op (Arrow.mk i)) ⋔ Arrow.mk p) := by
  let sq₀ := Functor.PullbackObjObj.ofHasPullback
    (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SimplicialSpace.{u}) i p
  change Arrow.mk sq.π ≅ Arrow.mk sq₀.π
  exact Functor.PullbackObjObj.π_iso_of_iso_left
    (G := internalHom)
    (f₁ := Arrow.mk i) (f₁' := Arrow.mk i) (f₃ := Arrow.mk p)
    sq sq₀ (Iso.refl (Arrow.mk i))

/-- The full original supplied presheaf pullback-power of a cofibration against a fibration
is a fibration in the named Reedy model. -/
theorem cartesian_pullbackObjObj_fibration
    {A B X Y : SimplicialSpace.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      fibrations SimplicialSpace.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi hp
  apply ((fibrations SimplicialSpace.{u}).arrow_mk_iso_iff (pullbackObjObjIso i p sq)).2
  exact pullbackHom_axiom.2.2 i p hi hp

/-- The same supplied full pullback-power is trivial when the original cofibration is weak. -/
theorem cartesian_pullbackObjObj_trivial_of_left
    {A B X Y : SimplicialSpace.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    trivialCofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      trivialFibrations SimplicialSpace.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi hp
  apply ((trivialFibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (pullbackObjObjIso i p sq)).2
  exact pullbackHom_axiom.2.1 i p hi hp

/-- The same supplied full pullback-power is trivial when the original fibration is weak. -/
theorem cartesian_pullbackObjObj_trivial_of_right
    {A B X Y : SimplicialSpace.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i → trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SimplicialSpace.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi hp
  apply ((trivialFibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (pullbackObjObjIso i p sq)).2
  exact pullbackHom_axiom.1 i p hi hp

/-- The actual Reedy model satisfies the Cartesian pushout-product and genuine terminal-unit
axioms for the transported presheaf closed structure. -/
theorem cartesian_isClosedSymmetricMonoidalModelCategory :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : IsCofibrant (𝟙_ SimplicialSpace.{u}) := isCofibrant _
  exact isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    SimplicialSpace.{u}
    (by
      intro A B K L i j hi hj
      exact pushoutProduct_axiom.1 i j hi hj)
    (by
      intro A B K L i j hi hj
      exact pushoutProduct_axiom.2.1 i j hi hj)
    (by
      intro A B K L i j hi hj
      exact pushoutProduct_axiom.2.2 i j hi hj)

end SimplicialSpace.ReedyModel
