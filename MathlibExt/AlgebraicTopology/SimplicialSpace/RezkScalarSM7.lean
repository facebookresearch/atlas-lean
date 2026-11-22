/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkScalarPushoutProducts
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory

/-!
# Full inner SM7 for the named Rezk model

All three supplied inner pushout-product laws and all three supplied
pullback-Hom laws concern the same named Rezk model and scalar Kan–Quillen
model. The dual laws use global lifting classes and the native parametrized
adjunction with the actual chosen squares and both strict filler equations.
The original arrows have no endpoint completeness or fibrancy assumptions.
Source: Rezk, *A model for the homotopy theory of homotopy theory*,
Section 2.5 and Theorem 7.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace.RezkModel

private theorem mono_of_cofibration {A B : SimplicialSpace.{u}} (i : A ⟶ B) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i → Mono i := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi
  change modelCategory.categoryWithCofibrations.cofibrations i at hi
  rw [modelCategory_cofibrations] at hi
  exact hi

private theorem mono_of_scalar_cofibration {K L : SSet.{u}} (j : K ⟶ L) :
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SSet.{u} j → Mono j := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hj
  let _ : Cofibration j := (HomotopicalAlgebra.cofibration_iff j).2 hj
  exact SSet.modelCategoryQuillen.mono_of_cofibration j

private theorem monicWeak_rlp_of_fibration {U V : SimplicialSpace.{u}} (p : U ⟶ V) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    fibrations SimplicialSpace.{u} p →
      (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences).rlp p := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hp
  change modelCategory.categoryWithFibrations.fibrations p at hp
  rwa [modelCategory_fibrations] at hp

/-- Cofibrations in both named models give a cofibration of the same supplied inner corner. -/
theorem inner_pushoutObjObj_cofibration
    {A B : SimplicialSpace.{u}} {K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → cofibrations SSet.{u} j →
      cofibrations SimplicialSpace.{u} pp.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hj
  let _ : Mono i := mono_of_cofibration i hi
  let _ : Mono j := mono_of_scalar_cofibration j hj
  change modelCategory.categoryWithCofibrations.cofibrations pp.ι
  rw [modelCategory_cofibrations]
  exact SimplicialSpace.inner_pushoutObjObj_mono i j pp

/-- A Rezk-trivial space cofibration makes the same supplied inner corner Rezk-trivial. -/
theorem inner_pushoutObjObj_trivialCofibration_of_left
    {A B : SimplicialSpace.{u}} {K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    trivialCofibrations SimplicialSpace.{u} i → cofibrations SSet.{u} j →
      trivialCofibrations SimplicialSpace.{u} pp.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hj
  have hpp := inner_pushoutObjObj_cofibration i j pp hi.1 hj
  have hi' := hi
  rw [modelCategory_trivialCofibrations] at hi' ⊢
  let _ : Mono i := hi'.1
  let _ : Mono j := mono_of_scalar_cofibration j hj
  exact ⟨mono_of_cofibration pp.ι hpp,
    SimplicialSpace.inner_pushoutObjObj_rezkWeak_of_left i j pp hi'.2⟩

/-- A scalar Kan-trivial cofibration makes the same supplied inner corner Rezk-trivial. -/
theorem inner_pushoutObjObj_trivialCofibration_of_right
    {A B : SimplicialSpace.{u}} {K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (pp : innerTensorBifunctor.PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → trivialCofibrations SSet.{u} j →
      trivialCofibrations SimplicialSpace.{u} pp.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hj
  have hpp := inner_pushoutObjObj_cofibration i j pp hi hj.1
  let _ : Mono i := mono_of_cofibration i hi
  let _ : Mono j := mono_of_scalar_cofibration j hj.1
  rw [modelCategory_trivialCofibrations]
  exact ⟨mono_of_cofibration pp.ι hpp,
    SimplicialSpace.inner_pushoutObjObj_rezkWeak_of_right i j pp hj.2⟩

/-- Full inner SM7 gives a Kan fibration for every actual supplied pullback-Hom square. -/
theorem inner_pullbackHom_fibration
    {A B U V : SimplicialSpace.{u}} (i : A ⟶ B) (p : U ⟶ V)
    (sq : innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      fibrations SSet.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hp
  have hpRLP := monicWeak_rlp_of_fibration p hp
  rw [← trivialCofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout innerTensorBifunctor i j
  have hpp := inner_pushoutObjObj_trivialCofibration_of_right i j pp hi hj
  rw [modelCategory_trivialCofibrations] at hpp
  exact (innerTensorHomAdjunction₂.hasLiftingProperty_iff pp sq).1 (hpRLP pp.ι hpp)

/-- A Rezk-trivial original space cofibration makes the whole supplied pullback-Hom Kan-trivial. -/
theorem inner_pullbackHom_trivialFibration_of_left
    {A B U V : SimplicialSpace.{u}} (i : A ⟶ B) (p : U ⟶ V)
    (sq : innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    trivialCofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      trivialFibrations SSet.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hp
  have hpRLP := monicWeak_rlp_of_fibration p hp
  rw [← cofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout innerTensorBifunctor i j
  have hpp := inner_pushoutObjObj_trivialCofibration_of_left i j pp hi hj
  rw [modelCategory_trivialCofibrations] at hpp
  exact (innerTensorHomAdjunction₂.hasLiftingProperty_iff pp sq).1 (hpRLP pp.ι hpp)

/-- A true Rezk trivial fibration makes the same supplied pullback-Hom Kan-trivial. -/
theorem inner_pullbackHom_trivialFibration_of_right
    {A B U V : SimplicialSpace.{u}} (i : A ⟶ B) (p : U ⟶ V)
    (sq : innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SSet.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hp
  let _ : Mono i := mono_of_cofibration i hi
  have hpI : ReedyGeneratingFamilies.I.{u}.rlp p := by
    rwa [modelCategory_trivialFibrations] at hp
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have hiR : cofibrations SimplicialSpace.{u} i :=
    (HomotopicalAlgebra.cofibration_iff i).1
      ((ReedyModel.cofibration_iff i).2 inferInstance)
  have hpR : trivialFibrations SimplicialSpace.{u} p := by
    rwa [← ReedyGeneratingFamilies.I_rlp_eq_trivialFibrations]
  exact ReedyModel.inner_pullbackHom_trivialFibration_of_right i p sq hiR hpR

end SimplicialSpace.RezkModel
