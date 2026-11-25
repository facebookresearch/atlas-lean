/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsEvaluation

/-!
# Actual substitution of whole relative words

Original functors and whole new-arrow images substitute through every
finite relative word. Identity and composition are genuine substitution
laws. A scalar operator whose individual new-arrow images have length at
most one preserves the entire length filtration, even when some images
are original length-zero Hom arrows.
-/

universe u v w uD vD wD uE vE wE
open CategoryTheory

namespace CategoryTheory.RelativeWords

variable {C : Type u} [Category.{v} C] {G : C → C → Type w}
  {D : Type uD} [Category.{vD} D] {K : D → D → Type wD}

/-- Substitute the actual original functor and whole supplied new-arrow images into a whole
relative word. -/
def substitute (F : C ⥤ D)
    (e : ∀ {a b : C}, G a b → Word K (F.obj a) (F.obj b)) {a b : C} (p : Word G a b) :
    Word K (F.obj a) (F.obj b) :=
  @eval C (inferInstance : Category.{v} C) G D
    (@category D (inferInstance : Category.{vD} D) K)
    (@Functor.comp C (inferInstance : Category.{v} C) D (inferInstance : Category.{vD} D) D
      (@category D (inferInstance : Category.{vD} D) K) F
      (@oldFunctor D (inferInstance : Category.{vD} D) K)) e a b p

/-- Original Hom segments substitute by the same original functor. -/
theorem substitute_old (F : C ⥤ D)
    (e : ∀ {a b : C}, G a b → Word K (F.obj a) (F.obj b)) {a b : C} (f : a ⟶ b) :
    substitute F e (Word.old f) = Word.old (F.map f) := rfl

/-- Substitution retains the actual original first segment, new-arrow image and whole
remaining word. -/
theorem substitute_cons (F : C ⥤ D)
    (e : ∀ {a b : C}, G a b → Word K (F.obj a) (F.obj b))
    {a x y b : C} (f : a ⟶ x) (g : G x y) (p : Word G y b) :
    substitute F e (Word.cons f g p) =
      Word.comp (Word.old (F.map f)) (Word.comp (e g) (substitute F e p)) := rfl

/-- Substitution preserves every whole original concatenation. -/
theorem substitute_comp (F : C ⥤ D)
    (e : ∀ {a b : C}, G a b → Word K (F.obj a) (F.obj b))
    {a b c : C} (p : Word G a b) (q : Word G b c) :
    substitute F e (Word.comp p q) = Word.comp (substitute F e p) (substitute F e q) :=
  @eval_comp C (inferInstance : Category.{v} C) G D
    (@category D (inferInstance : Category.{vD} D) K)
    (@Functor.comp C (inferInstance : Category.{v} C) D (inferInstance : Category.{vD} D) D
      (@category D (inferInstance : Category.{vD} D) K) F
      (@oldFunctor D (inferInstance : Category.{vD} D) K)) e a b c p q

/-- Each supplied original generator substitutes as its same whole new-arrow image. -/
theorem substitute_generator (F : C ⥤ D)
    (e : ∀ {a b : C}, G a b → Word K (F.obj a) (F.obj b)) {a b : C} (g : G a b) :
    substitute F e (generator G g) = e g :=
  @eval_generator C (inferInstance : Category.{v} C) G D
    (@category D (inferInstance : Category.{vD} D) K)
    (@Functor.comp C (inferInstance : Category.{v} C) D (inferInstance : Category.{vD} D) D
      (@category D (inferInstance : Category.{vD} D) K) F
      (@oldFunctor D (inferInstance : Category.{vD} D) K)) e a b g

/-- Individual length-zero or length-one new-arrow images preserve the full original word
filtration. -/
theorem length_substitute_le (F : C ⥤ D)
    (e : ∀ {a b : C}, G a b → Word K (F.obj a) (F.obj b))
    (he : ∀ {a b : C} (g : G a b), (e g).length ≤ 1) {a b : C} (p : Word G a b) :
    (substitute F e p).length ≤ p.length := by
  induction p with
  | old f => exact Nat.le_refl 0
  | cons f g p ih =>
      rw [substitute_cons, Word.length_comp, Word.length_comp]
      change 0 + ((e g).length + (substitute F e p).length) ≤ p.length + 1
      simpa only [Nat.zero_add] using
        (Nat.add_le_add (he g) ih).trans_eq (Nat.add_comm 1 p.length)

/-- Substituting the original identity and same new generators fixes every whole relative word. -/
theorem substitute_id {a b : C} (p : Word G a b) : substitute (𝟭 C) (generator G) p = p := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      rw [substitute_cons, ih]
      exact (Word.assoc (Word.old f) (generator G g) p).symm.trans (cons_eq_comp G f g p).symm

variable {E : Type uE} [Category.{vE} E] {L : E → E → Type wE}

/-- Two actual substitutions compose on every entire original word and its individual endpoints. -/
theorem substitute_substitute (F : C ⥤ D) (H : D ⥤ E)
    (e : ∀ {a b : C}, G a b → Word K (F.obj a) (F.obj b))
    (d : ∀ {a b : D}, K a b → Word L (H.obj a) (H.obj b)) {a b : C} (p : Word G a b) :
    substitute (F ⋙ H) (fun g => substitute H d (e g)) p = substitute H d (substitute F e p) := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      simp only [substitute_cons, substitute_comp, substitute_old, ih]
      rfl

end CategoryTheory.RelativeWords
