/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.ScalarCorners
public import MathlibExt.Topology.Category.PointedCGWH.CurrentCanonicalSmashSM7
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeDataComparison

/-!
# Scalar pushout-products for the actual original native projective model

The original model at the caller's original B/κ/I/J is used directly.
Full evaluated cotensor corners and genuine scalar lifting prove all
three projective pushout-product clauses, including their entire
original generated left classes. No projective SM7 dictionary is input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed
open CategoryTheory.EnrichedFunctorCat.ScalarLeibniz

namespace HomotopicalAlgebra.EnrichedProjective.Native.ScalarCompatibility

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

attribute [local instance] Native.modelCategory

/-- The selected scalar-compatible model is the original model at the
actual caller bottom, also equal to its fixed original constructor. -/
theorem model_eq_original_construction :
    Native.modelCategory (B := B) (A := A) = Construction.modelCategory (A := A) :=
  (Construction.modelCategory_eq_native (B := B)).symm

/-- Every actual enriched cotensor pullback corner is projectively
fibrant by the genuine base smash SM7 and every original component map. -/
theorem pullbackCotensor_fibration
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (p : F ⟶ G)
    (hi : cofibrations PointedCGWH.{u, v} i)
    (hp : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p)
    (sq : cotensorBifunctor.PullbackObjObj i p) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) sq.π := by
  rw [Native.fibrations_eq] at hp ⊢
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v}) sq.π).2
  intro a
  have hpa := (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v}) p).1 hp a
  exact PointedCGWH.CurrentCanonicalSmashSM7.fibration
    i (EnrichedFunctorCat.component p a) hi hpa (evaluatedPullbackSquare i p sq a)

/-- A trivial original coefficient makes every actual enriched
cotensor corner projectively trivial fibrant. -/
theorem pullbackCotensor_trivial_left
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (p : F ⟶ G)
    (hi : trivialCofibrations PointedCGWH.{u, v} i)
    (hp : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p)
    (sq : cotensorBifunctor.PullbackObjObj i p) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) sq.π := by
  rw [Native.fibrations_eq] at hp
  rw [Native.trivialFibrations_eq]
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (trivialFibrations PointedCGWH.{u, v}) sq.π).2
  intro a
  have hpa := (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v}) p).1 hp a
  exact PointedCGWH.CurrentCanonicalSmashSM7.trivial_left
    i (EnrichedFunctorCat.component p a) hi hpa (evaluatedPullbackSquare i p sq a)

/-- A trivial original projective fibration makes the same actual
cotensor corner projectively trivial fibrant. -/
theorem pullbackCotensor_trivial_right
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (p : F ⟶ G)
    (hi : cofibrations PointedCGWH.{u, v} i)
    (hp : trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p)
    (sq : cotensorBifunctor.PullbackObjObj i p) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) sq.π := by
  rw [Native.trivialFibrations_eq] at hp ⊢
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (trivialFibrations PointedCGWH.{u, v}) sq.π).2
  intro a
  have hpa := (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (trivialFibrations PointedCGWH.{u, v}) p).1 hp a
  exact PointedCGWH.CurrentCanonicalSmashSM7.trivial_right
    i (EnrichedFunctorCat.component p a) hi hpa (evaluatedPullbackSquare i p sq a)

/-- The whole actual scalar pushout-product is projectively cofibrant
on the complete original I-generated left class. -/
theorem scalarPushoutProduct_cofibration
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G)
    (hi : cofibrations PointedCGWH.{u, v} i)
    (hj : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j)
    (sq : tensorBifunctor.PushoutObjObj i j) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) sq.ι := by
  rw [← trivialFibrations_llp]
  intro X Y p hp
  let pb := pullbackSquare i p
  have hpb := pullbackCotensor_trivial_right i p hi hp pb
  rw [← cofibrations_rlp] at hpb
  exact
    (CategoryTheory.EnrichedFunctorCat.ScalarLeibniz.parametrizedAdjunction.hasLiftingProperty_iff
      sq pb).mpr
    (hpb j hj)

/-- A trivial original scalar coefficient makes the whole native
projective scalar pushout-product trivial cofibrant. -/
theorem scalarPushoutProduct_trivial_left
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G)
    (hi : trivialCofibrations PointedCGWH.{u, v} i)
    (hj : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j)
    (sq : tensorBifunctor.PushoutObjObj i j) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) sq.ι := by
  rw [← fibrations_llp]
  intro X Y p hp
  let pb := pullbackSquare i p
  have hpb := pullbackCotensor_trivial_left i p hi hp pb
  rw [← cofibrations_rlp] at hpb
  exact
    (CategoryTheory.EnrichedFunctorCat.ScalarLeibniz.parametrizedAdjunction.hasLiftingProperty_iff
      sq pb).mpr
    (hpb j hj)

/-- A trivial original projective cofibration makes the actual scalar
pushout-product trivial cofibrant on the whole original J-left class. -/
theorem scalarPushoutProduct_trivial_right
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G)
    (hi : cofibrations PointedCGWH.{u, v} i)
    (hj : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j)
    (sq : tensorBifunctor.PushoutObjObj i j) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) sq.ι := by
  rw [← fibrations_llp]
  intro X Y p hp
  let pb := pullbackSquare i p
  have hpb := pullbackCotensor_fibration i p hi hp pb
  rw [← trivialCofibrations_rlp] at hpb
  exact
    (CategoryTheory.EnrichedFunctorCat.ScalarLeibniz.parametrizedAdjunction.hasLiftingProperty_iff
      sq pb).mpr
    (hpb j hj)

/-- Actual scalar cofibration compatibility at every member of the
literal original free-I family, without coefficient cofibrancy input. -/
theorem original_free_I_scalar_cofibration
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G)
    (hi : cofibrations PointedCGWH.{u, v} i)
    (hj : generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v} j)
    (sq : tensorBifunctor.PushoutObjObj i j) :
    (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp sq.ι := by
  have hj' : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j := by
    rw [Native.cofibrations_eq]
    exact (generators PointedCGWH.realizedBoundaryInclusions).le_llp_rlp j hj
  have h := scalarPushoutProduct_cofibration i j hi hj' sq
  rwa [Native.cofibrations_eq] at h

/-- Actual scalar triviality at every member of the literal original
free-J family, preserving the original source generator arrow. -/
theorem original_free_J_scalar_trivial
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} A} (j : F ⟶ G)
    (hi : cofibrations PointedCGWH.{u, v} i)
    (hj : generators (A := A) PointedCGWH.realizedHornInclusions.{u, v} j)
    (sq : tensorBifunctor.PushoutObjObj i j) :
    (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp sq.ι := by
  have hj' : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) j := by
    rw [Native.trivialCofibrations_eq]
    exact (generators PointedCGWH.realizedHornInclusions).le_llp_rlp j hj
  have h := scalarPushoutProduct_trivial_right i j hi hj' sq
  rwa [Native.trivialCofibrations_eq] at h

/-- Fixed native scalar cotensor preserves original pointwise fibrations. -/
private theorem cotensor_fibration (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (p : X ⟶ Y)
    (hp : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      ((CategoryTheory.EnrichedFunctorCat.cotensor M).map p) := by
  rw [Native.fibrations_eq] at hp ⊢
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v}) _).2
  intro a
  have hpa := (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v}) p).1 hp a
  let sq := Functor.PullbackObjObj.ofIsInitial MonoidalClosed.internalHom
    (initial.to M) (EnrichedFunctorCat.component p a) initialIsInitial
  have h := PointedCGWH.CurrentCanonicalSmashSM7.fibration (initial.to M)
    (EnrichedFunctorCat.component p a) ((cofibration_iff _).mp inferInstance) hpa sq
  change fibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component
    ((CategoryTheory.EnrichedFunctorCat.cotensor M).map p) a)
  rw [CategoryTheory.EnrichedFunctorCat.cotensorMap_component]
  exact h

/-- Fixed native scalar cotensor preserves original pointwise trivial fibrations. -/
private theorem cotensor_trivial_fibration (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (p : X ⟶ Y)
    (hp : trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) p) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      ((CategoryTheory.EnrichedFunctorCat.cotensor M).map p) := by
  rw [Native.trivialFibrations_eq] at hp ⊢
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations PointedCGWH.{u, v}) _).2
  intro a
  have hpa := (EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations PointedCGWH.{u, v}) p).1 hp a
  let sq := Functor.PullbackObjObj.ofIsInitial MonoidalClosed.internalHom
    (initial.to M) (EnrichedFunctorCat.component p a) initialIsInitial
  have h := PointedCGWH.CurrentCanonicalSmashSM7.trivial_right (initial.to M)
    (EnrichedFunctorCat.component p a) ((cofibration_iff _).mp inferInstance) hpa sq
  change trivialFibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component
    ((CategoryTheory.EnrichedFunctorCat.cotensor M).map p) a)
  rw [CategoryTheory.EnrichedFunctorCat.cotensorMap_component]
  exact h

/-- The shared actual tensor/cotensor adjunction is Quillen for every cofibrant scalar. -/
theorem scalar_isQuillen (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    (CategoryTheory.EnrichedFunctorCat.ScalarLeibniz.adjunction (A := A) M).IsQuillenAdjunction :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (fun _ _ p hp => cotensor_fibration M p hp)
    (fun _ _ p hp => cotensor_trivial_fibration M p hp)

end HomotopicalAlgebra.EnrichedProjective.Native.ScalarCompatibility
