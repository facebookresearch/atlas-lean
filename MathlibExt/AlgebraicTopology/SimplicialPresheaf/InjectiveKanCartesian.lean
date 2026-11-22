/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanModel
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
import MathlibExt.AlgebraicTopology.ModelCategory.Proper
import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Cartesian compatibility of the actual injective Kan model

The original supplied Cartesian pushout corners are evaluated at each original
site object. The resulting scalar Kan–Quillen laws and the literal global
class dictionaries prove the three Cartesian clauses. The closed dual uses
the actual presheaf under-end, and properness and generation retain the same
selected model and common cardinal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory MonoidalClosed HomotopicalAlgebra Opposite
open scoped MonoidalCategory Simplicial SSet.modelCategoryQuillen

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The actual original under-end provides the presheaf closed structure. -/
scoped instance monoidalClosed : MonoidalClosed (SimplicialPresheaf.{u} D) where
  closed A := {
    rightAdj := SimplicialPresheaf.underHomFunctor.obj (op A)
    adj := SimplicialPresheaf.underHomAdjunction A }

open scoped SimplicialPresheaf.InjectiveKan

attribute [local instance] modelCategory

private def evaluatedPushout
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j) (d : Dᵒᵖ) :
    (curriedTensor SSet.{u}).PushoutObjObj (i.app d) (j.app d) where
  pt := sq.pt.obj d
  inl := sq.inl.app d
  inr := sq.inr.app d
  isPushout := sq.isPushout.map ((evaluation Dᵒᵖ SSet.{u}).obj d)
  ι := sq.ι.app d
  inl_ι := congrArg (fun f => f.app d) sq.inl_ι
  inr_ι := congrArg (fun f => f.app d) sq.inr_ι

private def evaluatedPushoutIso
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j) (d : Dᵒᵖ) :
    Arrow.mk (sq.ι.app d) ≅ (Arrow.mk (i.app d) □ Arrow.mk (j.app d)) := by
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (i.app d) (j.app d)
  change Arrow.mk (evaluatedPushout i j sq d).ι ≅ Arrow.mk sq₀.ι
  exact Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SSet.{u})
    (f₁ := Arrow.mk (i.app d)) (f₁' := Arrow.mk (i.app d))
    (f₂ := Arrow.mk (j.app d)) (evaluatedPushout i j sq d) sq₀ (Iso.refl _)

private theorem cofibration_iff_components {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) :
    cofibrations (SimplicialPresheaf.{u} D) i ↔ ∀ d, cofibrations SSet.{u} (i.app d) := by
  change (data D).model.categoryWithCofibrations.cofibrations i ↔ _
  rw [(data D).cofibrations_eq]
  change Mono i ↔ _
  rw [NatTrans.mono_iff_mono_app]
  constructor
  · intro hi d
    exact (HomotopicalAlgebra.cofibration_iff _).mp
      (SSet.modelCategoryQuillen.cofibration_of_mono _)
  · intro hi d
    let : Cofibration (i.app d) := (HomotopicalAlgebra.cofibration_iff _).mpr (hi d)
    exact SSet.modelCategoryQuillen.mono_of_cofibration _

private theorem weakEquivalence_iff_components {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) :
    weakEquivalences (SimplicialPresheaf.{u} D) i ↔ ∀ d, weakEquivalences SSet.{u} (i.app d) := by
  change (data D).model.categoryWithWeakEquivalences.weakEquivalences i ↔ _
  rw [(data D).weakEquivalences_eq]
  rfl

/-- Every original supplied Cartesian corner of two cofibrations is a cofibration. -/
theorem cartesian_pushoutObjObj_cofibration
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hj : cofibrations (SimplicialPresheaf.{u} D) j) :
    cofibrations (SimplicialPresheaf.{u} D) sq.ι := by
  apply (cofibration_iff_components sq.ι).mpr
  intro d
  let : Cofibration (i.app d) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr ((cofibration_iff_components i).mp hi d)
  let : Cofibration (j.app d) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr ((cofibration_iff_components j).mp hj d)
  apply ((cofibrations SSet.{u}).arrow_mk_iso_iff (evaluatedPushoutIso i j sq d)).mpr
  exact (HomotopicalAlgebra.cofibration_iff _).mp (SSet.cofibration_pushoutProduct _ _)

/-- The same original supplied corner is trivial when its left cofibration is weak. -/
theorem cartesian_pushoutObjObj_trivial_of_left
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j)
    (hi : trivialCofibrations (SimplicialPresheaf.{u} D) i)
    (hj : cofibrations (SimplicialPresheaf.{u} D) j) :
    trivialCofibrations (SimplicialPresheaf.{u} D) sq.ι := by
  refine ⟨cartesian_pushoutObjObj_cofibration i j sq hi.1 hj, ?_⟩
  apply (weakEquivalence_iff_components sq.ι).mpr
  intro d
  let : Cofibration (i.app d) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr ((cofibration_iff_components i).mp hi.1 d)
  let : Cofibration (j.app d) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr ((cofibration_iff_components j).mp hj d)
  let : WeakEquivalence (i.app d) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr ((weakEquivalence_iff_components i).mp hi.2 d)
  apply ((weakEquivalences SSet.{u}).arrow_mk_iso_iff (evaluatedPushoutIso i j sq d)).mpr
  exact (SSet.pushoutProduct_mem_trivialCofibrations_of_left _ _).2

/-- The same original supplied corner is trivial when its right cofibration is weak. -/
theorem cartesian_pushoutObjObj_trivial_of_right
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hj : trivialCofibrations (SimplicialPresheaf.{u} D) j) :
    trivialCofibrations (SimplicialPresheaf.{u} D) sq.ι := by
  refine ⟨cartesian_pushoutObjObj_cofibration i j sq hi hj.1, ?_⟩
  apply (weakEquivalence_iff_components sq.ι).mpr
  intro d
  let : Cofibration (i.app d) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr ((cofibration_iff_components i).mp hi d)
  let : Cofibration (j.app d) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr ((cofibration_iff_components j).mp hj.1 d)
  let : WeakEquivalence (j.app d) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr ((weakEquivalence_iff_components j).mp hj.2 d)
  apply ((weakEquivalences SSet.{u}).arrow_mk_iso_iff (evaluatedPushoutIso i j sq d)).mpr
  exact (SSet.pushoutProduct_mem_trivialCofibrations_of_right _ _).2

/-- All three actual Cartesian pushout-product laws hold on the original carrier. -/
theorem cartesianPushoutProductAxiom :
    CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B K L i j hi hj
    exact cartesian_pushoutObjObj_cofibration i j
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor (SimplicialPresheaf.{u} D)) i j) hi hj
  · intro A B K L i j hi hj
    exact cartesian_pushoutObjObj_trivial_of_left i j
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor (SimplicialPresheaf.{u} D)) i j) hi hj
  · intro A B K L i j hi hj
    exact cartesian_pushoutObjObj_trivial_of_right i j
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor (SimplicialPresheaf.{u} D)) i j) hi hj

/-- The global closed dual is formed with the actual original under-end Hom. -/
theorem cartesianPullbackHomAxiom :
    CartesianPullbackHomAxiom (C := SimplicialPresheaf.{u} D) :=
  HomotopicalAlgebra.cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp
    cartesianPushoutProductAxiom

private def pullbackObjObjIso
    {A B X Y : SimplicialPresheaf.{u} D} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤
      SimplicialPresheaf.{u} D).PullbackObjObj i p) :
    Arrow.mk sq.π ≅ ((op (Arrow.mk i)) ⋔ Arrow.mk p) := by
  let sq₀ := Functor.PullbackObjObj.ofHasPullback
    (internalHom : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤
      SimplicialPresheaf.{u} D) i p
  change Arrow.mk sq.π ≅ Arrow.mk sq₀.π
  exact Functor.PullbackObjObj.π_iso_of_iso_left (G := internalHom)
    (f₁ := Arrow.mk i) (f₁' := Arrow.mk i) (f₃ := Arrow.mk p) sq sq₀ (Iso.refl _)

/-- The actual supplied full pullback-Hom against a global injective fibration is fibrational. -/
theorem cartesian_pullbackObjObj_fibration
    {A B X Y : SimplicialPresheaf.{u} D} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤
      SimplicialPresheaf.{u} D).PullbackObjObj i p)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hp : fibrations (SimplicialPresheaf.{u} D) p) :
    fibrations (SimplicialPresheaf.{u} D) sq.π := by
  apply ((fibrations (SimplicialPresheaf.{u} D)).arrow_mk_iso_iff
    (pullbackObjObjIso i p sq)).mpr
  exact cartesianPullbackHomAxiom.2.2 i p hi hp

/-- The original supplied pullback-Hom is trivial when the left cofibration is weak. -/
theorem cartesian_pullbackObjObj_trivial_of_left
    {A B X Y : SimplicialPresheaf.{u} D} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤
      SimplicialPresheaf.{u} D).PullbackObjObj i p)
    (hi : trivialCofibrations (SimplicialPresheaf.{u} D) i)
    (hp : fibrations (SimplicialPresheaf.{u} D) p) :
    trivialFibrations (SimplicialPresheaf.{u} D) sq.π := by
  apply ((trivialFibrations (SimplicialPresheaf.{u} D)).arrow_mk_iso_iff
    (pullbackObjObjIso i p sq)).mpr
  exact cartesianPullbackHomAxiom.2.1 i p hi hp

/-- The original supplied pullback-Hom is trivial against a global trivial fibration. -/
theorem cartesian_pullbackObjObj_trivial_of_right
    {A B X Y : SimplicialPresheaf.{u} D} (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤
      SimplicialPresheaf.{u} D).PullbackObjObj i p)
    (hi : cofibrations (SimplicialPresheaf.{u} D) i)
    (hp : trivialFibrations (SimplicialPresheaf.{u} D) p) :
    trivialFibrations (SimplicialPresheaf.{u} D) sq.π := by
  apply ((trivialFibrations (SimplicialPresheaf.{u} D)).arrow_mk_iso_iff
    (pullbackObjObjIso i p sq)).mpr
  exact cartesianPullbackHomAxiom.1 i p hi hp

/-- The original terminal tensor unit itself is a valid cofibrant unit replacement. -/
theorem cartesian_isClosedSymmetricMonoidalModelCategory :
    IsClosedSymmetricMonoidalModelCategory (SimplicialPresheaf.{u} D) := by
  let : IsCofibrant (𝟙_ (SimplicialPresheaf.{u} D)) := (data D).all_cofibrant _
  exact isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    (SimplicialPresheaf.{u} D)
    (by intro A B K L i j hi hj; exact (cartesianPushoutProductAxiom (D := D)).1 i j hi hj)
    (by intro A B K L i j hi hj; exact (cartesianPushoutProductAxiom (D := D)).2.1 i j hi hj)
    (by intro A B K L i j hi hj; exact (cartesianPushoutProductAxiom (D := D)).2.2 i j hi hj)

/-- The same actual injective model is left proper by its proved universal cofibrancy. -/
theorem isLeftProper : IsLeftProper (SimplicialPresheaf.{u} D) :=
  isLeftProper_of_all_objects_cofibrant (data D).all_cofibrant

/-- Combinatoriality retains the model constructor's exact families and common cardinal. -/
theorem isCombinatorialModelCategory : IsCombinatorialModelCategory.{u}
    (SimplicialPresheaf.{u} D) := by
  let q := data.{u} D
  refine ⟨?_⟩
  exact ⟨q.κ, q.regular, q.bottom, q.locallyPresentable, ⟨q.generation⟩⟩

end SimplicialPresheaf.InjectiveKan
