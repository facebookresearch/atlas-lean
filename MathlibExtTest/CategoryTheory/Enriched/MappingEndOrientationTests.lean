/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.MappingEndOrientation
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd
public import MathlibExt.Topology.Category.PointedCGWH.Closed
import Batteries.Tactic.Lint

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory BraidedCategory MappingEndOrientationProbe
open scoped MonoidalClosed

namespace MappingEndOrientationTests

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {W F : EnrichedFunctor V A V} {K : V}

set_option maxHeartbeats 200000 in
example : True := by
  fail_if_success letI : Category A := inferInstance
  fail_if_success letI : SymmetricCategory V := inferInstance
  trivial

set_option maxHeartbeats 200000 in
example (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a)) (a b : A)
    (h : (β_ (a ⟶[V] b) K).inv ≫ (W.map a b ⊗ₘ p b) ≫
      eComp V (W.obj a) (W.obj b) (F.obj b) =
        (p a ⊗ₘ F.map a b) ≫ eComp V (W.obj a) (F.obj a) (F.obj b)) :
    MonoidalClosed.curry (endLeft p a b) = MonoidalClosed.curry (endRight p a b) :=
  (reverseAmbientNaturality_iff_endRelation p a b).1 h

set_option maxHeartbeats 200000 in
example (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a))
    (h : ∀ a b, MonoidalClosed.curry (endLeft p a b) =
      MonoidalClosed.curry (endRight p a b)) :
    ∀ (a b : A), (β_ (a ⟶[V] b) K).inv ≫ (W.map a b ⊗ₘ p b) ≫
      eComp V (W.obj a) (W.obj b) (F.obj b) =
        (p a ⊗ₘ F.map a b) ≫ eComp V (W.obj a) (F.obj a) (F.obj b) :=
  fun a b => (reverseAmbientNaturality_iff_endRelation p a b).2 (h a b)

set_option maxHeartbeats 200000 in
example [CategoryTheory.Limits.HasProduct (Enriched.weightedEnd.objects W F)]
    [CategoryTheory.Limits.HasProduct (Enriched.weightedEnd.relations W F)]
    [CategoryTheory.Limits.HasEqualizer (Enriched.weightedEnd.leftMap W F)
      (Enriched.weightedEnd.rightMap W F)] :
    GradedNatTrans (@Center.ofBraidedObj V _ _ (reverseBraiding V) (Enriched.weightedEnd W F)) W F :=
  reverseGradeOfEndRelations (Enriched.weightedEnd.π W F)
    (Enriched.weightedEnd.condition W F)

section Symmetric

variable {S : Type uV} [Category.{vV} S] [MonoidalCategory S]
  [SymmetricCategory S] [MonoidalClosed S]
  {C : Type uA} [EnrichedCategory S C]
  {Wₛ Fₛ : EnrichedFunctor S C S} {M : S}

set_option maxHeartbeats 200000 in
example (t : GradedNatTrans ((Center.ofBraided S).obj M) Wₛ Fₛ) (a b : C) :
    MonoidalClosed.curry (endLeft (fun a => t.app a) a b) =
      MonoidalClosed.curry (endRight (fun a => t.app a) a b) :=
  (canonicalNaturality_iff_endRelation (fun a => t.app a) a b).1 (t.naturality a b)

set_option maxHeartbeats 200000 in
example (p : ∀ a, M ⟶ (ihom (Wₛ.obj a)).obj (Fₛ.obj a))
    (h : ∀ a b, MonoidalClosed.curry (endLeft p a b) =
      MonoidalClosed.curry (endRight p a b)) :
    GradedNatTrans ((Center.ofBraided S).obj M) Wₛ Fₛ where
  app := p
  naturality a b := (canonicalNaturality_iff_endRelation p a b).2 (h a b)

end Symmetric

section Native

set_option maxHeartbeats 200000 in
example (K H : PointedCGWH.{uV, vV}) :
    (((Center.ofBraided PointedCGWH.{uV, vV}).obj K).2.β H).hom =
      ((@Center.ofBraidedObj PointedCGWH.{uV, vV} _ _ (reverseBraiding _) K).2.β H).hom := by
  change (β_ K H).hom = (β_ H K).inv
  exact SymmetricCategory.braiding_swap_eq_inv_braiding H K

variable {J : Type uA} [EnrichedCategory PointedCGWH.{uV, vV} J]
  (Wₚ Fₚ : EnrichedFunctor PointedCGWH.{uV, vV} J PointedCGWH.{uV, vV})

set_option maxHeartbeats 200000 in
example [CategoryTheory.Limits.HasProduct (Enriched.weightedEnd.objects Wₚ Fₚ)]
    [CategoryTheory.Limits.HasProduct (Enriched.weightedEnd.relations Wₚ Fₚ)]
    [CategoryTheory.Limits.HasEqualizer (Enriched.weightedEnd.leftMap Wₚ Fₚ)
      (Enriched.weightedEnd.rightMap Wₚ Fₚ)] :
    GradedNatTrans
      ((Center.ofBraided PointedCGWH.{uV, vV}).obj (Enriched.weightedEnd Wₚ Fₚ)) Wₚ Fₚ where
  app := Enriched.weightedEnd.π Wₚ Fₚ
  naturality a b :=
    (canonicalNaturality_iff_endRelation (Enriched.weightedEnd.π Wₚ Fₚ) a b).2
      (Enriched.weightedEnd.condition Wₚ Fₚ a b)

end Native

#print axioms reverseAmbientGrade_halfBraiding
#print axioms reverseGradeOfEndRelations
#print axioms reverseGradeOfEndRelations_app
#print axioms endLeft
#print axioms endRight
#print axioms reverseAmbientNaturality_iff_endRelation
#print axioms canonicalNaturality_iff_endRelation
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.MappingEndOrientation

end MappingEndOrientationTests
