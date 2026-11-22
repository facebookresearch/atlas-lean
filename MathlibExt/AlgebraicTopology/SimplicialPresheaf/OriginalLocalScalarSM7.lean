/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalSmithModel
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarSM7
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarLeibnizHom
import MathlibExt.CategoryTheory.LiftingProperties.LeibnizMate

/-!
# Scalar SM7 for the original localized presheaf model

All supplied pushout and pullback corners retain their original structural
arrows. The scalar weak branch is proved from the actual raw local tests;
the end and cotensor duals use the same constructed global lifting classes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory MonoidalClosed HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i}

private def suppliedPushoutIso
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j) :
    Arrow.mk pp.ι ≅ Arrow.mk (scalarPushoutObjObj i j).ι := by
  let c := scalarPushoutObjObj i j
  let e : pp.pt ≅ c.pt := IsPushout.isoIsPushout _ _ pp.isPushout c.isPushout
  have h : e.hom ≫ c.ι = pp.ι := by
    apply pp.hom_ext
    · dsimp only [e]
      rw [← Category.assoc, IsPushout.inl_isoIsPushout_hom]
      exact c.inl_ι.trans pp.inl_ι.symm
    · dsimp only [e]
      rw [← Category.assoc, IsPushout.inr_isoIsPushout_hom]
      exact c.inr_ι.trans pp.inr_ι.symm
  exact Arrow.isoMk e (Iso.refl _) (by
    change e.hom ≫ c.ι = pp.ι ≫ 𝟙 _
    simpa only [Category.comp_id] using h)

section BaseProof

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

private theorem baseCofOfMono {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (hi : monomorphisms (SimplicialPresheaf.{u} D) i) :
    cofibrations (SimplicialPresheaf.{u} D) i := by
  change (data D).model.categoryWithCofibrations.cofibrations i
  rw [(data D).cofibrations_eq]
  exact hi

private theorem monoOfBaseCof {A B : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (hi : cofibrations (SimplicialPresheaf.{u} D) i) :
    monomorphisms (SimplicialPresheaf.{u} D) i := by
  change (data D).model.categoryWithCofibrations.cofibrations i at hi
  rw [(data D).cofibrations_eq] at hi
  exact hi

private theorem pushoutMono
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j)
    (hi : monomorphisms (SimplicialPresheaf.{u} D) i)
    (hj : cofibrations SSet.{u} j) :
    monomorphisms (SimplicialPresheaf.{u} D) pp.ι :=
  monoOfBaseCof _ (scalar_pushoutObjObj_cofibration i j pp (baseCofOfMono i hi) hj)

private theorem canonicalPushoutLocalTrivial
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (hi : localTrivialMonomorphisms S i) (hj : cofibrations SSet.{u} j) :
    localTrivialMonomorphisms S (scalarPushoutObjObj i j).ι := by
  refine ⟨pushoutMono i j _ hi.1 hj, ?_⟩
  intro Z hZ
  let _ : Fibration (innerHomPre i Z) := (fibration_iff _).mpr
    (rawPrecomp_fibration_of_cofibration i Z (baseCofOfMono i hi.1) hZ.1)
  let _ : WeakEquivalence (innerHomPre i Z) := (weakEquivalence_iff _).mpr (hi.2 Z hZ)
  let _ : Cofibration j := (cofibration_iff _).mpr hj
  have htf := SSet.ihomToPullback_mem_trivialFibrations_of_right j (innerHomPre i Z)
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (scalarLeibnizHomIso i j Z)).mpr htf.2

private theorem pushoutLocalTrivialOfLeft
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j)
    (hi : localTrivialMonomorphisms S i) (hj : cofibrations SSet.{u} j) :
    localTrivialMonomorphisms S pp.ι := by
  have hc := canonicalPushoutLocalTrivial S i j hi hj
  rw [localTrivialMonomorphisms_eq_llp] at hc ⊢
  exact (((localWeakRightTests S).llp).arrow_mk_iso_iff (suppliedPushoutIso i j pp)).mpr hc

private theorem pushoutLocalTrivialOfRight
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j)
    (hi : monomorphisms (SimplicialPresheaf.{u} D) i)
    (hj : trivialCofibrations SSet.{u} j) :
    localTrivialMonomorphisms S pp.ι := by
  have hc := scalar_pushoutObjObj_trivialCofibration_of_right i j pp (baseCofOfMono i hi) hj
  exact ⟨monoOfBaseCof _ hc.1, weakEquivalences_le_originalLocalEquivalences S _ hc.2⟩

end BaseProof

omit [Small.{u} D] [LocallySmall.{u} D] in
private def tensorScalarTransformation {K L : SSet.{u}} (j : K ⟶ L) :
    scalarTensorFixed (D := D) K ⟶ scalarTensorFixed (D := D) L where
  app A := (scalarTensor.obj A).map j
  naturality _ _ i := ((scalarTensor.map i).naturality j).symm

omit [Small.{u} D] [LocallySmall.{u} D] in
set_option backward.isDefEq.respectTransparency false in
private theorem cotensorMate_eq {K L : SSet.{u}} (j : K ⟶ L) :
    conjugateEquiv (scalarTensorCotensorAdjunction (D := D) L)
        (scalarTensorCotensorAdjunction (D := D) K) (tensorScalarTransformation j) =
      (scalarCotensor (D := D)).map j.op := by
  apply NatTrans.ext
  funext Z
  apply ((scalarTensorCotensorAdjunction (D := D) K).homEquiv _ Z).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  ext d : 2
  dsimp only [tensorScalarTransformation, scalarTensorFixed] at ⊢
  simp only [NatTrans.comp_app, scalarTensorCotensorAdjunction_counit_app,
    scalarTensor_scalar_map, scalarCotensor_obj]
  change ((ihom L).obj (Z.obj d) ◁ j) ≫
      (β_ L ((ihom L).obj (Z.obj d))).inv ≫ (ihom.ev L).app (Z.obj d) =
    ((pre j).app (Z.obj d) ▷ K) ≫
      (β_ K ((ihom K).obj (Z.obj d))).inv ≫ (ihom.ev K).app (Z.obj d)
  rw [BraidedCategory.braiding_inv_naturality_right_assoc,
    BraidedCategory.braiding_inv_naturality_left_assoc]
  exact congrArg (fun g => (β_ K ((ihom L).obj (Z.obj d))).inv ≫ g)
    (id_tensor_pre_app_comp_ev j (Z.obj d)).symm

omit [Small.{u} D] [LocallySmall.{u} D] in
private def walkingTensorPushout
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j) :
    (parallelPair (tensorScalarTransformation j) (tensorScalarTransformation j)).PushoutObjObj
      WalkingParallelPairHom.left i where
  pt := pp.pt
  inl := pp.inr
  inr := pp.inl
  isPushout := pp.isPushout.flip
  ι := pp.ι
  inl_ι := pp.inr_ι
  inr_ι := pp.inl_ι

omit [Small.{u} D] [LocallySmall.{u} D] in
set_option backward.isDefEq.respectTransparency false in
private theorem cotensorLifting_iff
    {A B X Y : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (p : X ⟶ Y)
    (pp : scalarTensor.PushoutObjObj i j)
    (q : (walkingParallelPairOp.leftOp ⋙
      parallelPair ((scalarCotensor (D := D)).map j.op)
        ((scalarCotensor (D := D)).map j.op)).PullbackObjObj WalkingParallelPairHom.left p) :
    HasLiftingProperty pp.ι p ↔ HasLiftingProperty i q.π := by
  generalize hβ : (scalarCotensor (D := D)).map j.op = β at q ⊢
  have hβ' : β = conjugateEquiv (scalarTensorCotensorAdjunction (D := D) L)
      (scalarTensorCotensorAdjunction (D := D) K) (tensorScalarTransformation j) :=
    hβ.symm.trans (cotensorMate_eq j).symm
  clear hβ
  subst β
  simpa only [walkingTensorPushout, scalarTensorFixed_obj] using
      Adjunction.leibnizMate_hasLiftingProperty_iff_of
    (scalarTensorCotensorAdjunction (D := D) K)
    (scalarTensorCotensorAdjunction (D := D) L) (tensorScalarTransformation j)
    (walkingTensorPushout i j pp) q

variable [Small.{u} I]

private theorem localCof_iff
    (S : I → Arrow (SimplicialPresheaf.{u} D)) {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations (SimplicialPresheaf.{u} D) i ↔ monomorphisms (SimplicialPresheaf.{u} D) i := by
  change (originalLocalSmithData S).model.categoryWithCofibrations.cofibrations i ↔ _
  rw [(originalLocalSmithData S).cofibrations_eq]

private theorem localTrivialCof_iff
    (S : I → Arrow (SimplicialPresheaf.{u} D)) {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    trivialCofibrations (SimplicialPresheaf.{u} D) i ↔ localTrivialMonomorphisms S i := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  rw [(originalLocalSmithData S).trivialCofibrations_eq]

private theorem localFib_iff
    (S : I → Arrow (SimplicialPresheaf.{u} D)) {A B : SimplicialPresheaf.{u} D} (p : A ⟶ B) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    fibrations (SimplicialPresheaf.{u} D) p ↔ (localTrivialMonomorphisms S).rlp p := by
  change (originalLocalSmithData S).model.categoryWithFibrations.fibrations p ↔ _
  rw [(originalLocalSmithData S).fibrations_eq]

private theorem localTrivialFib_iff
    (S : I → Arrow (SimplicialPresheaf.{u} D)) {A B : SimplicialPresheaf.{u} D} (p : A ⟶ B) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    trivialFibrations (SimplicialPresheaf.{u} D) p ↔
      (monomorphisms (SimplicialPresheaf.{u} D)).rlp p := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  rw [(originalLocalSmithData S).trivialFibrations_eq]

/-- Every supplied scalar pushout of cofibrations is a cofibration in the same original-S model. -/
theorem localized_scalar_pushoutObjObj_cofibration
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations (SimplicialPresheaf.{u} D) i → cofibrations SSet.{u} j →
      cofibrations (SimplicialPresheaf.{u} D) pp.ι := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hj
  exact (localCof_iff S _).mpr (pushoutMono i j pp ((localCof_iff S i).mp hi) hj)

/-- Localized triviality on the presheaf input gives triviality of the same supplied scalar
pushout. -/
theorem localized_scalar_pushoutObjObj_trivialCofibration_of_left
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    trivialCofibrations (SimplicialPresheaf.{u} D) i → cofibrations SSet.{u} j →
      trivialCofibrations (SimplicialPresheaf.{u} D) pp.ι := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hj
  exact (localTrivialCof_iff S _).mpr
    (pushoutLocalTrivialOfLeft S i j pp ((localTrivialCof_iff S i).mp hi) hj)

/-- Scalar Kan triviality gives localized triviality of the same supplied scalar pushout. -/
theorem localized_scalar_pushoutObjObj_trivialCofibration_of_right
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : scalarTensor.PushoutObjObj i j) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations (SimplicialPresheaf.{u} D) i → trivialCofibrations SSet.{u} j →
      trivialCofibrations (SimplicialPresheaf.{u} D) pp.ι := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hj
  exact (localTrivialCof_iff S _).mpr
    (pushoutLocalTrivialOfRight S i j pp ((localCof_iff S i).mp hi) hj)

/-- Every supplied original end pullback of a cofibration and GLOBAL localized fibration is Kan
fibrational. -/
theorem localized_scalar_pullbackObjObj_fibration
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B X Y : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (p : X ⟶ Y) (q : innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations (SimplicialPresheaf.{u} D) i → fibrations (SimplicialPresheaf.{u} D) p →
      fibrations SSet.{u} q.π := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hp
  rw [← trivialCofibrations_rlp]
  intro K L j hj
  let pp := scalarPushoutObjObj i j
  have hpp := localized_scalar_pushoutObjObj_trivialCofibration_of_right S i j pp hi hj
  exact ((scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff pp q).mp
    (((localFib_iff S p).mp hp) pp.ι ((localTrivialCof_iff S _).mp hpp))

/-- Localized triviality of the input cofibration gives scalar triviality in the SAME supplied end
pullback. -/
theorem localized_scalar_pullbackObjObj_trivialFibration_of_left
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B X Y : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (p : X ⟶ Y) (q : innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    trivialCofibrations (SimplicialPresheaf.{u} D) i → fibrations (SimplicialPresheaf.{u} D) p →
      trivialFibrations SSet.{u} q.π := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hp
  rw [← cofibrations_rlp]
  intro K L j hj
  let pp := scalarPushoutObjObj i j
  have hpp := localized_scalar_pushoutObjObj_trivialCofibration_of_left S i j pp hi hj
  exact ((scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff pp q).mp
    (((localFib_iff S p).mp hp) pp.ι ((localTrivialCof_iff S _).mp hpp))

/-- A GLOBAL localized trivial fibration gives scalar triviality in the SAME supplied end
pullback. -/
theorem localized_scalar_pullbackObjObj_trivialFibration_of_right
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B X Y : SimplicialPresheaf.{u} D}
    (i : A ⟶ B) (p : X ⟶ Y) (q : innerHomFunctor.PullbackObjObj i p) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations (SimplicialPresheaf.{u} D) i → trivialFibrations (SimplicialPresheaf.{u} D) p →
      trivialFibrations SSet.{u} q.π := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hp
  rw [← cofibrations_rlp]
  intro K L j hj
  let pp := scalarPushoutObjObj i j
  have hpp := localized_scalar_pushoutObjObj_cofibration S i j pp hi hj
  exact ((scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff pp q).mp
    (((localTrivialFib_iff S p).mp hp) pp.ι ((localCof_iff S _).mp hpp))

/-- The SAME supplied scalar cotensor corner is GLOBAL localized fibrational for every original
input fibration. -/
theorem localized_cotensor_pullbackObjObj_fibration
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {K L : SSet.{u}} {X Y : SimplicialPresheaf.{u} D} (j : K ⟶ L) (p : X ⟶ Y)
    (q : (walkingParallelPairOp.leftOp ⋙
      parallelPair ((scalarCotensor (D := D)).map j.op)
        ((scalarCotensor (D := D)).map j.op)).PullbackObjObj WalkingParallelPairHom.left p) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations SSet.{u} j → fibrations (SimplicialPresheaf.{u} D) p →
      fibrations (SimplicialPresheaf.{u} D) q.π := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hj hp
  apply (localFib_iff S _).mpr
  intro A B i hi
  let pp := scalarPushoutObjObj i j
  have hpp := localized_scalar_pushoutObjObj_trivialCofibration_of_left S i j pp
    ((localTrivialCof_iff S i).mpr hi) hj
  exact (cotensorLifting_iff i j p pp q).mp
    (((localFib_iff S p).mp hp) pp.ι ((localTrivialCof_iff S _).mp hpp))

/-- Scalar triviality gives GLOBAL localized triviality of the SAME supplied cotensor corner. -/
theorem localized_cotensor_pullbackObjObj_trivialFibration_of_left
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {K L : SSet.{u}} {X Y : SimplicialPresheaf.{u} D} (j : K ⟶ L) (p : X ⟶ Y)
    (q : (walkingParallelPairOp.leftOp ⋙
      parallelPair ((scalarCotensor (D := D)).map j.op)
        ((scalarCotensor (D := D)).map j.op)).PullbackObjObj WalkingParallelPairHom.left p) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    trivialCofibrations SSet.{u} j → fibrations (SimplicialPresheaf.{u} D) p →
      trivialFibrations (SimplicialPresheaf.{u} D) q.π := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hj hp
  apply (localTrivialFib_iff S _).mpr
  intro A B i hi
  let pp := scalarPushoutObjObj i j
  have hpp := localized_scalar_pushoutObjObj_trivialCofibration_of_right S i j pp
    ((localCof_iff S i).mpr hi) hj
  exact (cotensorLifting_iff i j p pp q).mp
    (((localFib_iff S p).mp hp) pp.ι ((localTrivialCof_iff S _).mp hpp))

/-- GLOBAL localized input triviality gives GLOBAL triviality of the SAME supplied cotensor
corner. -/
theorem localized_cotensor_pullbackObjObj_trivialFibration_of_right
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {K L : SSet.{u}} {X Y : SimplicialPresheaf.{u} D} (j : K ⟶ L) (p : X ⟶ Y)
    (q : (walkingParallelPairOp.leftOp ⋙
      parallelPair ((scalarCotensor (D := D)).map j.op)
        ((scalarCotensor (D := D)).map j.op)).PullbackObjObj WalkingParallelPairHom.left p) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations SSet.{u} j → trivialFibrations (SimplicialPresheaf.{u} D) p →
      trivialFibrations (SimplicialPresheaf.{u} D) q.π := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hj hp
  apply (localTrivialFib_iff S _).mpr
  intro A B i hi
  let pp := scalarPushoutObjObj i j
  have hpp := localized_scalar_pushoutObjObj_cofibration S i j pp
    ((localCof_iff S i).mpr hi) hj
  exact (cotensorLifting_iff i j p pp q).mp
    (((localTrivialFib_iff S p).mp hp) pp.ι ((localCof_iff S _).mp hpp))

end SimplicialPresheaf.InjectiveKan
