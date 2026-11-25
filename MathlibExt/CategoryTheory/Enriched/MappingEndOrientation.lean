/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

/-!
# Weighted-end relations and graded naturality

The original weighted-end relation matches graded naturality for the center object
of the reversed braiding, with half-braiding at `H` given by `(β_ H M).inv`.
In the symmetric case this gives the canonical ambient-grade relation used by
native mapping objects.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.MappingEndOrientationProbe

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
theorem reverseAmbientGrade_halfBraiding (M H : V) :
    ((@Center.ofBraidedObj V _ _ (reverseBraiding V) M).2.β H).hom = (β_ H M).inv := rfl

variable [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {W F : EnrichedFunctor V A V} {K : V}

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
/-- The target-action side of the uncurried weighted-end relation. -/
def endLeft
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a)) (a b : A) :
    ((a ⟶[V] b) ⊗ W.obj a) ⊗ K ⟶ F.obj b :=
  (α_ (a ⟶[V] b) (W.obj a) K).hom ≫
    ((a ⟶[V] b) ◁ ((W.obj a) ◁ p a)) ≫
    ((a ⟶[V] b) ◁ (ihom.ev (W.obj a)).app (F.obj a)) ≫
    (β_ (a ⟶[V] b) (F.obj a)).hom ≫
    MonoidalClosed.uncurry (F.map a b)

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
/-- The source-action side of the uncurried weighted-end relation. -/
def endRight
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a)) (a b : A) :
    ((a ⟶[V] b) ⊗ W.obj a) ⊗ K ⟶ F.obj b :=
  (((β_ (a ⟶[V] b) (W.obj a)).hom ≫
      MonoidalClosed.uncurry (W.map a b)) ⊗ₘ 𝟙 K) ≫
    ((W.obj b) ◁ p b) ≫ (ihom.ev (W.obj b)).app (F.obj b)

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
private def sourceTransport (W : EnrichedFunctor V A V) (K : V) (a b : A) :
    ((a ⟶[V] b) ⊗ W.obj a) ⊗ K ⟶ W.obj a ⊗ (K ⊗ (a ⟶[V] b)) :=
  ((β_ (a ⟶[V] b) (W.obj a)).hom ▷ K) ≫
    (α_ (W.obj a) (a ⟶[V] b) K).hom ≫
    (W.obj a ◁ (β_ (a ⟶[V] b) K).hom)

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
private theorem transport_reverse_left
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a)) (a b : A) :
    sourceTransport W K a b ≫ MonoidalClosed.uncurry
        ((β_ (a ⟶[V] b) K).inv ≫ (W.map a b ⊗ₘ p b) ≫
          eComp V (W.obj a) (W.obj b) (F.obj b)) = endRight p a b := by
  dsimp only [sourceTransport, endRight]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eComp]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id]
  simp only [whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_assoc]
  simp only [tensorHom_id, comp_whiskerRight, Category.assoc,
    MonoidalClosed.uncurry_eq]

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
private theorem transport_right
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a)) (a b : A) :
    sourceTransport W K a b ≫ MonoidalClosed.uncurry
        ((p a ⊗ₘ F.map a b) ≫ eComp V (W.obj a) (F.obj a) (F.obj b)) =
      endLeft p a b := by
  have hhex :
      sourceTransport W K a b ≫ (α_ (W.obj a) K (a ⟶[V] b)).inv =
        (α_ (a ⟶[V] b) (W.obj a) K).hom ≫
          (β_ (a ⟶[V] b) (W.obj a ⊗ K)).hom := by
    rw [braiding_tensor_right_hom]
    simp only [sourceTransport, Category.assoc, Iso.hom_inv_id_assoc]
  rw [MonoidalClosed.uncurry_eComp]
  calc
    _ = (α_ (a ⟶[V] b) (W.obj a) K).hom ≫
          (β_ (a ⟶[V] b) (W.obj a ⊗ K)).hom ≫
          (MonoidalClosed.uncurry (p a) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (F.map a b) := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ (MonoidalClosed.uncurry (p a) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (F.map a b)) hhex
    _ = (α_ (a ⟶[V] b) (W.obj a) K).hom ≫
          ((a ⟶[V] b) ◁ MonoidalClosed.uncurry (p a)) ≫
          (β_ (a ⟶[V] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b) := by
      rw [← braiding_naturality_right_assoc]
    _ = endLeft p a b := by
      simp only [endLeft, MonoidalClosed.uncurry_eq, whiskerLeft_comp, Category.assoc]

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
theorem reverseAmbientNaturality_iff_endRelation
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a)) (a b : A) :
    ((β_ (a ⟶[V] b) K).inv ≫ (W.map a b ⊗ₘ p b) ≫
        eComp V (W.obj a) (W.obj b) (F.obj b) =
      (p a ⊗ₘ F.map a b) ≫ eComp V (W.obj a) (F.obj a) (F.obj b)) ↔
    (MonoidalClosed.curry (endLeft p a b) = MonoidalClosed.curry (endRight p a b)) := by
  constructor
  · intro h
    have hu := congrArg (MonoidalClosed.uncurry (A := W.obj a)) h
    have ht := congrArg (fun q => sourceTransport W K a b ≫ q) hu
    rw [transport_reverse_left, transport_right] at ht
    exact congrArg MonoidalClosed.curry ht.symm
  · intro h
    apply MonoidalClosed.uncurry_injective
    let _ : IsIso (sourceTransport W K a b) := by
      dsimp only [sourceTransport]
      infer_instance
    apply (cancel_epi (sourceTransport W K a b)).1
    rw [transport_reverse_left, transport_right]
    have hu := congrArg MonoidalClosed.uncurry h.symm
    simpa only [MonoidalClosed.uncurry_curry] using hu

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
/-- Construct reverse-grade naturality from the original weighted-end relations. -/
@[no_expose]
def reverseGradeOfEndRelations
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a))
    (h : ∀ a b, MonoidalClosed.curry (endLeft p a b) =
      MonoidalClosed.curry (endRight p a b)) :
    GradedNatTrans (@Center.ofBraidedObj V _ _ (reverseBraiding V) K) W F where
  app := p
  naturality a b := (reverseAmbientNaturality_iff_endRelation p a b).2 (h a b)

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
private theorem reverseGradeOfEndRelations_app_private
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a))
    (h : ∀ a b, MonoidalClosed.curry (endLeft p a b) =
      MonoidalClosed.curry (endRight p a b)) (a : A) :
    (reverseGradeOfEndRelations p h).app a = p a := rfl

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
theorem reverseGradeOfEndRelations_app
    (p : ∀ a, K ⟶ (ihom (W.obj a)).obj (F.obj a))
    (h : ∀ a b, MonoidalClosed.curry (endLeft p a b) =
      MonoidalClosed.curry (endRight p a b)) (a : A) :
    (reverseGradeOfEndRelations p h).app a = p a :=
  reverseGradeOfEndRelations_app_private p h a

section Symmetric

variable {S : Type uV} [Category.{vV} S] [MonoidalCategory S]
  [SymmetricCategory S] [MonoidalClosed S]
  {C : Type uA} [EnrichedCategory S C]
  {Wₛ Fₛ : EnrichedFunctor S C S} {M : S}

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the complete weighted-end orientation calculation.
theorem canonicalNaturality_iff_endRelation
    (p : ∀ a, M ⟶ (ihom (Wₛ.obj a)).obj (Fₛ.obj a)) (a b : C) :
    ((β_ M (a ⟶[S] b)).hom ≫ (Wₛ.map a b ⊗ₘ p b) ≫
        eComp S (Wₛ.obj a) (Wₛ.obj b) (Fₛ.obj b) =
      (p a ⊗ₘ Fₛ.map a b) ≫ eComp S (Wₛ.obj a) (Fₛ.obj a) (Fₛ.obj b)) ↔
    (MonoidalClosed.curry (endLeft p a b) = MonoidalClosed.curry (endRight p a b)) := by
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
  exact reverseAmbientNaturality_iff_endRelation p a b

end Symmetric








end CategoryTheory.MappingEndOrientationProbe
