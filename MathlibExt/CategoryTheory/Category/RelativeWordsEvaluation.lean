/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWords
import Mathlib.CategoryTheory.EqToHom

/-!
# Whole evaluation of actual relative words

An actual original functor and actual images of the new arrows evaluate
every whole relative word. The evaluation is a genuine functor on the
same original objects. Every functor out of the relative-word category
is recovered from its original restriction and individual new-arrow
images, including all original identity and composition maps.
-/

universe u v w uD vD
open CategoryTheory

namespace CategoryTheory.RelativeWords

variable {C : Type u} [Category.{v} C] (G : C → C → Type w)

/-- The actual new arrow, with both adjacent original identity segments retained. -/
def generator {a b : C} (g : G a b) : Word G a b :=
  Word.cons (𝟙 a) g (Word.old (𝟙 b))

/-- Every supplied new arrow has its literal length one, including loop pairs. -/
theorem generator_length {a b : C} (g : G a b) : (generator G g).length = 1 := rfl

/-- A whole relative word is the actual original first segment, new arrow and remaining word. -/
theorem cons_eq_comp {a x y b : C} (f : a ⟶ x) (g : G x y) (p : Word G y b) :
    Word.cons f g p = Word.comp (Word.comp (Word.old f) (generator G g)) p := by
  cases p <;> simp only [generator, Word.comp, Word.precompose, Category.comp_id, Category.id_comp]

variable {G} {D : Type uD} [Category.{vD} D]

/-- Evaluate every original segment and individually supplied new arrow by genuine target
composition. -/
def eval (F : C ⥤ D) (e : ∀ {a b : C}, G a b → (F.obj a ⟶ F.obj b)) :
    {a b : C} → Word G a b → (F.obj a ⟶ F.obj b)
  | _, _, .old f => F.map f
  | _, _, .cons f g p => F.map f ≫ e g ≫ eval F e p

/-- Whole evaluation preserves original precomposition. -/
theorem eval_precompose (F : C ⥤ D) (e : ∀ {a b : C}, G a b → (F.obj a ⟶ F.obj b))
    {a b c : C} (f : a ⟶ b) (p : Word G b c) :
    eval F e (Word.precompose f p) = F.map f ≫ eval F e p := by
  cases p with
  | old g => exact F.map_comp f g
  | cons g a p => simp only [Word.precompose, eval, F.map_comp, Category.assoc]

/-- Whole evaluation preserves every original concatenation. -/
theorem eval_comp (F : C ⥤ D) (e : ∀ {a b : C}, G a b → (F.obj a ⟶ F.obj b))
    {a b c : C} (p : Word G a b) (q : Word G b c) :
    eval F e (Word.comp p q) = eval F e p ≫ eval F e q := by
  induction p with
  | old f => exact eval_precompose F e f q
  | cons f g p ih =>
      change F.map f ≫ e g ≫ eval F e (Word.comp p q) =
        (F.map f ≫ e g ≫ eval F e p) ≫ eval F e q
      rw [ih, Category.assoc, Category.assoc]

/-- Whole evaluation reads each supplied new arrow back as its same actual target map. -/
theorem eval_generator (F : C ⥤ D) (e : ∀ {a b : C}, G a b → (F.obj a ⟶ F.obj b))
    {a b : C} (g : G a b) : eval F e (generator G g) = e g := by
  simp only [generator, eval, F.map_id, Category.id_comp, Category.comp_id]

/-- The actual relative-word evaluation functor retains the original object map. -/
def evalFunctor (F : C ⥤ D) (e : ∀ {a b : C}, G a b → (F.obj a ⟶ F.obj b)) :
    @Functor C (@category C (inferInstance : Category.{v} C) G) D
      (inferInstance : Category.{vD} D) :=
  @Functor.mk C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D) (fun a => F.obj a) (fun {_ _} p => eval F e p)
    (fun a => F.map_id a) (fun {_ _ _} p q => eval_comp F e p q)

/-- Apply a genuine relative-word functor with its exact source category dictionary. -/
def mapWord (H : @Functor C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D)) {a b : C} (p : Word G a b) :=
  @Functor.map C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D) H a b p

/-- Restrict a genuine relative-word functor to the same original category. -/
def restriction (H : @Functor C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D)) : C ⥤ D :=
  @Functor.comp C (inferInstance : Category.{v} C) C
    (@category C (inferInstance : Category.{v} C) G) D (inferInstance : Category.{vD} D)
    (@oldFunctor C (inferInstance : Category.{v} C) G) H

/-- The actual relative-word functor preserves whole word concatenation. -/
theorem mapWord_comp (H : @Functor C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D)) {a b c : C} (p : Word G a b) (q : Word G b c) :
    mapWord H (Word.comp p q) = mapWord H p ≫ mapWord H q :=
  @Functor.map_comp C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D) H a b c p q

/-- The original restriction and new-arrow values recover every whole relative word map. -/
theorem recover_eval (H : @Functor C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D)) {a b : C} (p : Word G a b) :
    eval (restriction H) (fun g => mapWord H (generator G g)) p = mapWord H p := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      change mapWord H (Word.old f) ≫ mapWord H (generator G g) ≫
          eval (restriction H) (fun g => mapWord H (generator G g)) p = mapWord H (Word.cons f g p)
      rw [ih, cons_eq_comp]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ mapWord H p) (mapWord_comp H (Word.old f) (generator G
          g)).symm).trans
          (mapWord_comp H (Word.comp (Word.old f) (generator G g)) p).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual whole relative-word functor is recovered, with its same objects and every
original map. -/
theorem recoverFunctor (H : @Functor C (@category C (inferInstance : Category.{v} C) G) D
  (inferInstance :
    Category.{vD} D)) :
    evalFunctor (restriction H) (fun g => mapWord H (generator G g)) = H := by
  apply @Functor.ext C (@category C (inferInstance : Category.{v} C) G) D
    (inferInstance : Category.{vD} D)
    (@evalFunctor C (inferInstance : Category.{v} C) G D (inferInstance : Category.{vD} D)
      (restriction H) (fun g => mapWord H (generator G g))) H (fun _ => rfl)
  intro a b p
  simpa only [evalFunctor, mapWord, restriction, oldFunctor, eqToHom_refl,
    Category.id_comp, Category.comp_id] using recover_eval H p

end CategoryTheory.RelativeWords
