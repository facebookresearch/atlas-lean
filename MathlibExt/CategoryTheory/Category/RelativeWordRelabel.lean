/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsSubstitution

/-!
# Actual relabelling of raw relative words

An original functor and actual new-arrow maps relabel every old segment
and individual new letter. Unlike attaching-domain reduction, each raw
letter remains a letter, so the exact finite word length is retained.
The original identity, composition and two-step relabelling laws follow
from the proved whole-word substitution operations.
-/

universe u v w uD vD wD uE vE wE
open CategoryTheory

namespace CategoryTheory.RelativeWords

variable {C : Type u} [Category.{v} C] {G : C → C → Type w}
  {D : Type uD} [Category.{vD} D] {K : D → D → Type wD}

/-- Relabel every whole raw word by the original functor and individually supplied arrow map. -/
def relabel (F : C ⥤ D) (m : ∀ {a b : C}, G a b → K (F.obj a) (F.obj b))
    {a b : C} (p : Word G a b) : Word K (F.obj a) (F.obj b) :=
  substitute F (fun g => generator K (m g)) p

/-- An original segment is relabelled by the same original functor. -/
theorem relabel_old (F : C ⥤ D) (m : ∀ {a b : C}, G a b → K (F.obj a) (F.obj b))
    {a b : C} (f : a ⟶ b) : relabel F m (Word.old f) = Word.old (F.map f) := rfl

/-- Relabelling preserves the complete original first segment, new letter and remaining raw word. -/
theorem relabel_cons (F : C ⥤ D) (m : ∀ {a b : C}, G a b → K (F.obj a) (F.obj b))
    {a x y b : C} (f : a ⟶ x) (g : G x y) (p : Word G y b) :
    relabel F m (Word.cons f g p) = Word.cons (F.map f) (m g) (relabel F m p) := by
  rw [relabel, substitute_cons]
  exact (Word.assoc _ _ _).symm.trans (cons_eq_comp _ _ _ _).symm

/-- Every original raw generator is relabelled to its same original target generator. -/
theorem relabel_generator (F : C ⥤ D) (m : ∀ {a b : C}, G a b → K (F.obj a) (F.obj b))
    {a b : C} (g : G a b) : relabel F m (generator G g) = generator K (m g) :=
  substitute_generator F _ g

/-- Relabelling preserves the exact finite number of original raw target letters. -/
theorem length_relabel (F : C ⥤ D) (m : ∀ {a b : C}, G a b → K (F.obj a) (F.obj b))
    {a b : C} (p : Word G a b) : (relabel F m p).length = p.length := by
  induction p with
  | old f => rfl
  | cons f g p ih => rw [relabel_cons]; exact congrArg (fun n => n + 1) ih

/-- Relabelling preserves whole original raw-word composition. -/
theorem relabel_comp (F : C ⥤ D) (m : ∀ {a b : C}, G a b → K (F.obj a) (F.obj b))
    {a b c : C} (p : Word G a b) (q : Word G b c) :
    relabel F m (Word.comp p q) = Word.comp (relabel F m p) (relabel F m q) :=
  substitute_comp F _ p q

/-- The original identity functor and identity arrow maps fix every complete raw word. -/
theorem relabel_id {a b : C} (p : Word G a b) : relabel (𝟭 C) (fun g => g) p = p := substitute_id p

variable {E : Type uE} [Category.{vE} E] {L : E → E → Type wE}

/-- Consecutive actual raw relabellings compose on every original word and endpoint. -/
theorem relabel_relabel (F : C ⥤ D) (H : D ⥤ E)
    (m : ∀ {a b : C}, G a b → K (F.obj a) (F.obj b))
    (n : ∀ {a b : D}, K a b → L (H.obj a) (H.obj b)) {a b : C} (p : Word G a b) :
    relabel H n (relabel F m p) = relabel (F ⋙ H) (fun g => n (m g)) p := by
  induction p with
  | old f => rfl
  | cons f g p ih => rw [relabel_cons, relabel_cons, relabel_cons, ih]; rfl

end CategoryTheory.RelativeWords
