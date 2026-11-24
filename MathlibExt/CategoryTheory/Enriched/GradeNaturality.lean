/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.GradedYoneda
public import MathlibExt.CategoryTheory.Enriched.GradedComposition
public import Mathlib.CategoryTheory.Monoidal.Center

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.GradedNatTrans

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalClosed V] {A : Type uA} [EnrichedCategory V A]
  (Γ : Center V) {F G : EnrichedFunctor V A V}

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
/-- The uncurried component of a graded natural transformation, with the grade moved
to the first tensor factor by its half-braiding. -/
def gradeFirstComponent (t : GradedNatTrans Γ F G) (a : A) :
    Γ.1 ⊗ F.obj a ⟶ G.obj a :=
  (Γ.2.β (F.obj a)).hom ≫ MonoidalClosed.uncurry (t.app a)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
private def gradeFirstSourceTransport (F : EnrichedFunctor V A V) (a b : A) :
    (Γ.1 ⊗ F.obj a) ⊗ (a ⟶[V] b) ⟶ F.obj a ⊗ (Γ.1 ⊗ (a ⟶[V] b)) :=
  ((Γ.2.β (F.obj a)).hom ▷ (a ⟶[V] b)) ≫
    (α_ (F.obj a) Γ.1 (a ⟶[V] b)).hom

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
private theorem gradeFirst_transport_left
    (p : ∀ a, Γ.1 ⟶ (ihom (F.obj a)).obj (G.obj a)) (a b : A) :
    gradeFirstSourceTransport Γ F a b ≫ MonoidalClosed.uncurry
        ((Γ.2.β (a ⟶[V] b)).hom ≫ (F.map a b ⊗ₘ p b) ≫
          eComp V (F.obj a) (F.obj b) (G.obj b)) =
      (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
        (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫
        (Γ.2.β (F.obj b)).hom ≫ MonoidalClosed.uncurry (p b) := by
  dsimp only [gradeFirstSourceTransport]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eComp]
  have hm :
      (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
          (Γ.2.β (F.obj a ⊗ (a ⟶[V] b))).hom =
        ((Γ.2.β (F.obj a)).hom ▷ (a ⟶[V] b)) ≫
          (α_ (F.obj a) Γ.1 (a ⟶[V] b)).hom ≫
          (F.obj a ◁ (Γ.2.β (a ⟶[V] b)).hom) ≫
          (α_ (F.obj a) (a ⟶[V] b) Γ.1).inv := by
    rw [HalfBraiding.monoidal]
    simp only [Iso.hom_inv_id_assoc]
  calc
    _ = (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
        (Γ.2.β (F.obj a ⊗ (a ⟶[V] b))).hom ≫
        (MonoidalClosed.uncurry (F.map a b) ▷ Γ.1) ≫
        MonoidalClosed.uncurry (p b) := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ (MonoidalClosed.uncurry (F.map a b) ▷ Γ.1) ≫
          MonoidalClosed.uncurry (p b)) hm.symm
    _ = _ := by rw [← HalfBraiding.naturality_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
private theorem gradeFirst_transport_right
    (p : ∀ a, Γ.1 ⟶ (ihom (F.obj a)).obj (G.obj a)) (a b : A) :
    gradeFirstSourceTransport Γ F a b ≫ MonoidalClosed.uncurry
        ((p a ⊗ₘ G.map a b) ≫ eComp V (F.obj a) (G.obj a) (G.obj b)) =
      (((Γ.2.β (F.obj a)).hom ≫ MonoidalClosed.uncurry (p a)) ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (G.map a b) := by
  dsimp only [gradeFirstSourceTransport]
  rw [MonoidalClosed.uncurry_eComp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
theorem gradeFirstNaturality_iff
    (p : ∀ a, Γ.1 ⟶ (ihom (F.obj a)).obj (G.obj a)) (a b : A) :
    ((Γ.2.β (a ⟶[V] b)).hom ≫ (F.map a b ⊗ₘ p b) ≫
        eComp V (F.obj a) (F.obj b) (G.obj b) =
      (p a ⊗ₘ G.map a b) ≫ eComp V (F.obj a) (G.obj a) (G.obj b)) ↔
    ((α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
        (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫
        (Γ.2.β (F.obj b)).hom ≫ MonoidalClosed.uncurry (p b) =
      (((Γ.2.β (F.obj a)).hom ≫ MonoidalClosed.uncurry (p a)) ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (G.map a b)) := by
  constructor
  · intro h
    have hu := congrArg (MonoidalClosed.uncurry (A := F.obj a)) h
    have ht := congrArg (fun q => gradeFirstSourceTransport Γ F a b ≫ q) hu
    rw [gradeFirst_transport_left, gradeFirst_transport_right] at ht
    exact ht
  · intro h
    apply MonoidalClosed.uncurry_injective
    let _ : IsIso (gradeFirstSourceTransport Γ F a b) := by
      dsimp only [gradeFirstSourceTransport]
      infer_instance
    apply (cancel_epi (gradeFirstSourceTransport Γ F a b)).1
    rw [gradeFirst_transport_left, gradeFirst_transport_right]
    exact h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
theorem gradeFirstComponent_naturality (t : GradedNatTrans Γ F G) (a b : A) :
    (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
        (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫ gradeFirstComponent Γ t b =
      (gradeFirstComponent Γ t a ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (G.map a b) :=
  (gradeFirstNaturality_iff Γ (fun a => t.app a) a b).1 (t.naturality a b)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
/-- Construct a graded natural transformation from grade-first tensor components
satisfying enriched naturality, using the inverse half-braiding and currying. -/
@[no_expose]
def ofGradeFirstComponents
    (q : ∀ a, Γ.1 ⊗ F.obj a ⟶ G.obj a)
    (hq : ∀ a b, (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
      (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫ q b =
      (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.map a b)) :
    GradedNatTrans Γ F G where
  app a := MonoidalClosed.curry ((Γ.2.β (F.obj a)).inv ≫ q a)
  naturality a b := by
    apply (gradeFirstNaturality_iff Γ
      (fun a => MonoidalClosed.curry ((Γ.2.β (F.obj a)).inv ≫ q a)) a b).2
    simpa only [MonoidalClosed.uncurry_curry, Category.assoc,
      Iso.hom_inv_id_assoc] using hq a b

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
private theorem ofGradeFirstComponents_app_private
    (q : ∀ a, Γ.1 ⊗ F.obj a ⟶ G.obj a)
    (hq : ∀ a b, (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
      (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫ q b =
      (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.map a b)) (a : A) :
    (ofGradeFirstComponents Γ q hq).app a =
      MonoidalClosed.curry ((Γ.2.β (F.obj a)).inv ≫ q a) := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
theorem ofGradeFirstComponents_app
    (q : ∀ a, Γ.1 ⊗ F.obj a ⟶ G.obj a)
    (hq : ∀ a b, (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
      (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫ q b =
      (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.map a b)) (a : A) :
    (ofGradeFirstComponents Γ q hq).app a =
      MonoidalClosed.curry ((Γ.2.β (F.obj a)).inv ≫ q a) :=
  ofGradeFirstComponents_app_private Γ q hq a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
theorem ofGradeFirstComponents_gradeFirstComponent
    (q : ∀ a, Γ.1 ⊗ F.obj a ⟶ G.obj a)
    (hq : ∀ a b, (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
      (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫ q b =
      (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.map a b)) (a : A) :
    gradeFirstComponent Γ (ofGradeFirstComponents Γ q hq) a = q a := by
  rw [gradeFirstComponent, ofGradeFirstComponents_app, MonoidalClosed.uncurry_curry]
  exact Iso.hom_inv_id_assoc _ _

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
theorem ofGradeFirstComponents_reconstruct (t : GradedNatTrans Γ F G) :
    ofGradeFirstComponents Γ (gradeFirstComponent Γ t)
      (fun a b => gradeFirstComponent_naturality Γ t a b) = t := by
  apply GradedNatTrans.ext
  funext a
  rw [ofGradeFirstComponents_app, gradeFirstComponent, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, MonoidalClosed.curry_uncurry]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
theorem gradeFirstComponent_ext (t t' : GradedNatTrans Γ F G)
    (h : ∀ a, gradeFirstComponent Γ t a = gradeFirstComponent Γ t' a) : t = t' := by
  apply GradedNatTrans.ext
  funext a
  apply MonoidalClosed.uncurry_injective
  apply (cancel_epi (Γ.2.β (F.obj a)).hom).1
  exact h a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched Hom and half-braiding calculation.
theorem gradeFirstComponent_regrade {Γ' : Center V} (u : Γ ⟶ Γ')
    (t : GradedNatTrans Γ' F G) (a : A) :
    gradeFirstComponent Γ (regrade u t) a =
      (u.f ▷ F.obj a) ≫ gradeFirstComponent Γ' t a := by
  dsimp only [gradeFirstComponent]
  rw [regrade_app, MonoidalClosed.uncurry_natural_left]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ MonoidalClosed.uncurry (t.app a)) (u.comm (F.obj a)).symm

end CategoryTheory.GradedNatTrans
