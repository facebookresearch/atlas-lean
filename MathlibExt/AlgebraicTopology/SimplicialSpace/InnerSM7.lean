/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# Inner pushout-products and pullback-Hom in the named Reedy model
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty MonoidalCategory
open scoped MonoidalCategory SimplicialSpace.Inner Simplicial

namespace SimplicialSpace.ReedyModel

private abbrev outerEvaluation (m : SimplexCategoryᵒᵖ) : SimplicialSpace.{u} ⥤ SSet.{u} :=
  SimplicialSpace.forget ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m

private def evaluatedPushout {X Y : SimplicialSpace.{u}} {K L : SSet.{u}}
    (i : X ⟶ Y) (j : K ⟶ L)
    (sq : SimplicialSpace.innerTensorBifunctor.PushoutObjObj i j)
    (m : SimplexCategoryᵒᵖ) :
    (curriedTensor SSet.{u}).PushoutObjObj (i.hom.app m) j where
  pt := sq.pt.diagram.obj m
  inl := sq.inl.hom.app m
  inr := sq.inr.hom.app m
  isPushout := sq.isPushout.map (outerEvaluation m)
  ι := sq.ι.hom.app m
  inl_ι := by
    exact congrArg (fun f => f.hom.app m) sq.inl_ι
  inr_ι := by
    exact congrArg (fun f => f.hom.app m) sq.inr_ι

private theorem scalarPushout_mono {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j)
    [Mono i] [Mono j] : Mono sq.ι := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  let _ : Cofibration j := SSet.modelCategoryQuillen.cofibration_of_mono j
  let canonical := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let e : sq.pt ≅ canonical.pt := sq.isPushout.isoIsPushout _ _ canonical.isPushout
  have he : sq.ι = e.hom ≫ canonical.ι := by
    apply sq.hom_ext
    · simp [e]
    · simp [e]
  let _ : Cofibration canonical.ι := by
    change Cofibration ((Arrow.mk i □ Arrow.mk j).hom)
    exact SSet.cofibration_pushoutProduct i j
  let _ : Mono canonical.ι := SSet.modelCategoryQuillen.mono_of_cofibration _
  rw [he]
  infer_instance

/-- Every supplied inner pushout-product of the two named cofibrations is a cofibration. -/
theorem inner_pushoutObjObj_cofibration
    {X Y : SimplicialSpace.{u}} {K L : SSet.{u}} (i : X ⟶ Y) (j : K ⟶ L)
    (sq : SimplicialSpace.innerTensorBifunctor.PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → cofibrations SSet.{u} j →
      cofibrations SimplicialSpace.{u} sq.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hj
  let _ : Cofibration i := (HomotopicalAlgebra.cofibration_iff i).2 hi
  let _ : Mono i := (cofibration_iff i).1 inferInstance
  let _ : Mono i.hom := (SimplicialSpace.mono_forget_map_iff i).2 inferInstance
  let _ : Cofibration j := (HomotopicalAlgebra.cofibration_iff j).2 hj
  let _ : Mono j := SSet.modelCategoryQuillen.mono_of_cofibration j
  have hmono : Mono (SimplicialSpace.forget.map sq.ι) := by
    apply (NatTrans.mono_iff_mono_app (SimplicialSpace.forget.map sq.ι)).2
    intro m
    change Mono (evaluatedPushout i j sq m).ι
    exact scalarPushout_mono (i.hom.app m) j (evaluatedPushout i j sq m)
  exact (HomotopicalAlgebra.cofibration_iff sq.ι).1
    ((cofibration_iff sq.ι).2 ((SimplicialSpace.mono_forget_map_iff sq.ι).1 hmono))

/-- A supplied inner pushout-product is trivial when its original Reedy factor is trivial. -/
theorem inner_pushoutObjObj_trivialCofibration_of_left
    {X Y : SimplicialSpace.{u}} {K L : SSet.{u}} (i : X ⟶ Y) (j : K ⟶ L)
    (sq : SimplicialSpace.innerTensorBifunctor.PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    trivialCofibrations SimplicialSpace.{u} i → cofibrations SSet.{u} j →
      trivialCofibrations SimplicialSpace.{u} sq.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hj
  refine ⟨inner_pushoutObjObj_cofibration i j sq hi.1 hj, ?_⟩
  let _ : Cofibration i := (HomotopicalAlgebra.cofibration_iff i).2 hi.1
  let _ : Mono i := (cofibration_iff i).1 inferInstance
  let _ : Mono i.hom := (SimplicialSpace.mono_forget_map_iff i).2 inferInstance
  let _ : Cofibration j := (HomotopicalAlgebra.cofibration_iff j).2 hj
  let _ : Mono j := SSet.modelCategoryQuillen.mono_of_cofibration j
  apply (HomotopicalAlgebra.weakEquivalence_iff sq.ι).1
  apply (weakEquivalence_iff sq.ι).2
  intro n
  have hn := (weakEquivalence_iff i).1
    ((HomotopicalAlgebra.weakEquivalence_iff i).2 hi.2) n
  let m := Opposite.op ⦋n⦌
  let _ : Cofibration (i.hom.app m) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  have ha : SSet.anodyneExtensions (i.hom.app m) := by
    rw [SSet.anodyneExtensions_eq_trivialCofibrations]
    exact ⟨(HomotopicalAlgebra.cofibration_iff _).1 inferInstance, hn⟩
  have h := SSet.anodyneExtensions_pushoutObjObjι' (evaluatedPushout i j sq m) ha
  rw [SSet.anodyneExtensions_eq_trivialCofibrations] at h
  exact h.2

/-- A supplied inner pushout-product is trivial when its original scalar factor is trivial. -/
theorem inner_pushoutObjObj_trivialCofibration_of_right
    {X Y : SimplicialSpace.{u}} {K L : SSet.{u}} (i : X ⟶ Y) (j : K ⟶ L)
    (sq : SimplicialSpace.innerTensorBifunctor.PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → trivialCofibrations SSet.{u} j →
      trivialCofibrations SimplicialSpace.{u} sq.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hj
  refine ⟨inner_pushoutObjObj_cofibration i j sq hi hj.1, ?_⟩
  let _ : Cofibration i := (HomotopicalAlgebra.cofibration_iff i).2 hi
  let _ : Mono i := (cofibration_iff i).1 inferInstance
  let _ : Mono i.hom := (SimplicialSpace.mono_forget_map_iff i).2 inferInstance
  have ha : SSet.anodyneExtensions j := by
    rwa [SSet.anodyneExtensions_eq_trivialCofibrations]
  apply (HomotopicalAlgebra.weakEquivalence_iff sq.ι).1
  apply (weakEquivalence_iff sq.ι).2
  intro n
  have h := SSet.anodyneExtensions_pushoutObjObjι
    (evaluatedPushout i j sq (Opposite.op ⦋n⦌)) ha
  rw [SSet.anodyneExtensions_eq_trivialCofibrations] at h
  exact h.2

/-- SM7 for the actual supplied inner pullback-Hom in the two named models. -/
theorem inner_pullbackHom_fibration
    {X Y U V : SimplicialSpace.{u}} (i : X ⟶ Y) (p : U ⟶ V)
    (sq : SimplicialSpace.innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      fibrations SSet.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hp
  rw [← trivialCofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout SimplicialSpace.innerTensorBifunctor i j
  have hpp := inner_pushoutObjObj_trivialCofibration_of_right i j pp hi hj
  let _ : Cofibration pp.ι := (HomotopicalAlgebra.cofibration_iff _).2 hpp.1
  let _ : WeakEquivalence pp.ι := (HomotopicalAlgebra.weakEquivalence_iff _).2 hpp.2
  let _ : Fibration p := (HomotopicalAlgebra.fibration_iff p).2 hp
  exact (SimplicialSpace.innerTensorHomAdjunction₂.hasLiftingProperty_iff pp sq).1
    (ModelCategory.cm4a pp.ι p)

/-- The actual inner pullback-Hom is Kan-trivial when the original left map is Reedy-trivial. -/
theorem inner_pullbackHom_trivialFibration_of_left
    {X Y U V : SimplicialSpace.{u}} (i : X ⟶ Y) (p : U ⟶ V)
    (sq : SimplicialSpace.innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    trivialCofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      trivialFibrations SSet.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hp
  rw [← cofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout SimplicialSpace.innerTensorBifunctor i j
  have hpp := inner_pushoutObjObj_trivialCofibration_of_left i j pp hi hj
  let _ : Cofibration pp.ι := (HomotopicalAlgebra.cofibration_iff _).2 hpp.1
  let _ : WeakEquivalence pp.ι := (HomotopicalAlgebra.weakEquivalence_iff _).2 hpp.2
  let _ : Fibration p := (HomotopicalAlgebra.fibration_iff p).2 hp
  exact (SimplicialSpace.innerTensorHomAdjunction₂.hasLiftingProperty_iff pp sq).1
    (ModelCategory.cm4a pp.ι p)

/-- The actual inner pullback-Hom is Kan-trivial when the original right map is Reedy-trivial. -/
theorem inner_pullbackHom_trivialFibration_of_right
    {X Y U V : SimplicialSpace.{u}} (i : X ⟶ Y) (p : U ⟶ V)
    (sq : SimplicialSpace.innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SSet.{u} sq.π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hp
  rw [← cofibrations_rlp]
  intro K L j hj
  let pp := Functor.PushoutObjObj.ofHasPushout SimplicialSpace.innerTensorBifunctor i j
  have hpp := inner_pushoutObjObj_cofibration i j pp hi hj
  let _ : Cofibration pp.ι := (HomotopicalAlgebra.cofibration_iff _).2 hpp
  let _ : Fibration p := (HomotopicalAlgebra.fibration_iff p).2 hp.1
  let _ : WeakEquivalence p := (HomotopicalAlgebra.weakEquivalence_iff p).2 hp.2
  exact (SimplicialSpace.innerTensorHomAdjunction₂.hasLiftingProperty_iff pp sq).1
    (ModelCategory.cm4b pp.ι p)

end SimplicialSpace.ReedyModel
