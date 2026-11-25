/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsEvaluation
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Free paths represented by actual relative words

Adding individual arrows to a free path category produces the free path
category on the original arrows and those new arrows. The two functors
below keep every original object, flatten complete original path segments,
and recover the normalized relative words. Both inverse equations are
proved on the full original paths and words, with independent universes.
-/

universe u v w
open CategoryTheory

namespace CategoryTheory.RelativeWords.FreePaths

variable {O : Type u} (Q : Quiver.{v} O) (G : O → O → Type w)

/-- The arrow family retains the actual old and new generators separately. -/
@[instance_reducible]
def sumQuiver : Quiver.{max v w} O where
  Hom a b := Q.Hom a b ⊕ G a b

/-- The original path category, with its original arrow dictionary. -/
structure Old (Q : Quiver.{v} O) where
  /-- The same individual original label. -/
  obj : O

/-- The combined path category, retaining the same individual labels. -/
structure Combined (Q : Quiver.{v} O) (G : O → O → Type w) where
  /-- The same individual original label. -/
  obj : O

/-- The relative-word category, retaining the same individual labels. -/
structure Relative (Q : Quiver.{v} O) (G : O → O → Type w) where
  /-- The same individual original label. -/
  obj : O

instance oldCategory : Category.{max u v} (Old Q) where
  Hom a b := @Quiver.Path O Q a.obj b.obj
  id a := @Quiver.Path.nil O Q a.obj
  comp {a b c} p q := @Quiver.Path.comp O Q a.obj b.obj c.obj p q
  id_comp p := @Quiver.Path.nil_comp O Q _ _ p
  comp_id p := @Quiver.Path.comp_nil O Q _ _ p
  assoc p q r := @Quiver.Path.comp_assoc O Q _ _ _ _ p q r

instance combinedCategory : Category.{max u v w} (Combined Q G) where
  Hom a b := @Quiver.Path O (sumQuiver Q G) a.obj b.obj
  id a := @Quiver.Path.nil O (sumQuiver Q G) a.obj
  comp {a b c} p q := @Quiver.Path.comp O (sumQuiver Q G) a.obj b.obj c.obj p q
  id_comp p := @Quiver.Path.nil_comp O (sumQuiver Q G) _ _ p
  comp_id p := @Quiver.Path.comp_nil O (sumQuiver Q G) _ _ p
  assoc p q r := @Quiver.Path.comp_assoc O (sumQuiver Q G) _ _ _ _ p q r

instance relativeCategory : Category.{max u v w} (Relative Q G) where
  Hom a b := @Word (Paths O) (@Paths.categoryPaths O Q) G a.obj b.obj
  id a := @Word.old (Paths O) (@Paths.categoryPaths O Q) G a.obj a.obj (@Quiver.Path.nil O Q a.obj)
  comp p q := @Word.comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _ p q
  id_comp p := @Word.id_comp (Paths O) (@Paths.categoryPaths O Q) G _ _ p
  comp_id p := @Word.comp_id (Paths O) (@Paths.categoryPaths O Q) G _ _ p
  assoc p q r := @Word.assoc (Paths O) (@Paths.categoryPaths O Q) G _ _ _ _ p q r

/-- Include each original arrow in the combined original arrow family. -/
def oldInclusion : @Prefunctor O Q O (sumQuiver Q G) :=
  @Prefunctor.mk O Q O (sumQuiver Q G) (fun a => a) (fun {_ _} e => Sum.inl e)

/-- Map every complete original path by the same generator inclusion. -/
def oldPath {a b : O} (p : @Quiver.Path O Q a b) :
    @Quiver.Path O (sumQuiver Q G) a b :=
  @Prefunctor.mapPath O Q O (sumQuiver Q G) (oldInclusion Q G) a b p

/-- The complete old-path inclusion preserves concatenation. -/
theorem oldPath_comp {a b c : O} (p : @Quiver.Path O Q a b) (r : @Quiver.Path O Q b c) :
    oldPath Q G (@Quiver.Path.comp O Q a b c p r) =
      @Quiver.Path.comp O (sumQuiver Q G) a b c (oldPath Q G p) (oldPath Q G r) :=
  @Prefunctor.mapPath_comp O Q O (sumQuiver Q G) (oldInclusion Q G) a b p c r

/-- Map complete original paths to complete paths on the combined arrow family. -/
def oldPaths : Old Q ⥤ Combined Q G where
  obj a := ⟨a.obj⟩
  map p := oldPath Q G p
  map_id _ := rfl
  map_comp p q := oldPath_comp Q G p q

/-- Complete old paths include as old normalized segments. -/
def oldWords : Old Q ⥤ Relative Q G where
  obj a := ⟨a.obj⟩
  map p := Word.old p
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original paths map to the combined native paths with the same original labels. -/
def oldNative : @Functor (Paths O) (@Paths.categoryPaths O Q) (Combined Q G)
    (combinedCategory Q G) where
  obj a := ⟨a⟩
  map p := oldPath Q G p
  map_id _ := rfl
  map_comp p q := oldPath_comp Q G p q

/-- Flatten a whole normalized relative word, retaining each individual new arrow. -/
def flattenWord {a b : O} (p : @Word (Paths O) (@Paths.categoryPaths O Q) G a b) :
    @Quiver.Path O (sumQuiver Q G) a b :=
  @eval (Paths O) (@Paths.categoryPaths O Q) G (Combined Q G) (combinedCategory Q G)
    (oldNative Q G)
    (fun {_ _} g => @Quiver.Hom.toPath O (sumQuiver Q G) _ _ (Sum.inr g)) a b p

/-- The whole-word flattening preserves concatenation. -/
theorem flattenWord_comp {a b c : O}
    (p : @Word (Paths O) (@Paths.categoryPaths O Q) G a b)
    (r : @Word (Paths O) (@Paths.categoryPaths O Q) G b c) :
    flattenWord Q G (@Word.comp (Paths O) (@Paths.categoryPaths O Q) G a b c p r) =
      @Quiver.Path.comp O (sumQuiver Q G) a b c (flattenWord Q G p) (flattenWord Q G r) :=
  @eval_comp (Paths O) (@Paths.categoryPaths O Q) G (Combined Q G) (combinedCategory Q G)
    (oldNative Q G) _ a b c p r

/-- Flatten the complete original segments and each supplied new arrow. -/
def flatten : Relative Q G ⥤ Combined Q G where
  obj a := ⟨a.obj⟩
  map p := flattenWord Q G p
  map_id _ := rfl
  map_comp p q := flattenWord_comp Q G p q

/-- Read an individual old arrow as its old singleton and a new arrow as its new letter. -/
def generatorWord {a b : O} : (sumQuiver Q G).Hom a b →
    @Word (Paths O) (@Paths.categoryPaths O Q) G a b
  | Sum.inl e => @Word.old (Paths O) (@Paths.categoryPaths O Q) G a b
      (@Quiver.Hom.toPath O Q a b e)
  | Sum.inr g => @RelativeWords.generator (Paths O) (@Paths.categoryPaths O Q) G a b g

/-- Read old arrows as original singleton segments and new arrows as new letters. -/
def generators : @Prefunctor O (sumQuiver Q G) (Relative Q G)
    (relativeCategory Q G).toQuiver :=
  @Prefunctor.mk O (sumQuiver Q G) (Relative Q G) (relativeCategory Q G).toQuiver
    (fun a => ⟨a⟩) (fun {_ _} e => generatorWord Q G e)

/-- Read a complete combined path as its whole normalized relative word. -/
def unflattenPath {a b : O} (p : @Quiver.Path O (sumQuiver Q G) a b) :
    @Word (Paths O) (@Paths.categoryPaths O Q) G a b := by
  letI := sumQuiver Q G
  exact @Quiver.Path.rec O (sumQuiver Q G) a
    (fun b _ => @Word (Paths O) (@Paths.categoryPaths O Q) G a b)
    (@Word.old (Paths O) (@Paths.categoryPaths O Q) G a a (@Quiver.Path.nil O Q a))
    (fun {_ _} _ e ih => @Word.comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _
      ih (generatorWord Q G e)) b p

/-- Reading a path preserves its complete concatenation. -/
theorem unflattenPath_comp {a b c : O}
    (p : @Quiver.Path O (sumQuiver Q G) a b) (r : @Quiver.Path O (sumQuiver Q G) b c) :
    unflattenPath Q G (@Quiver.Path.comp O (sumQuiver Q G) a b c p r) =
      @Word.comp (Paths O) (@Paths.categoryPaths O Q) G a b c
        (unflattenPath Q G p) (unflattenPath Q G r) := by
  induction r with
  | nil => exact (@Word.comp_id (Paths O) (@Paths.categoryPaths O Q) G _ _ _).symm
  | cons r e ih =>
      change @Word.comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _
        (unflattenPath Q G (@Quiver.Path.comp O (sumQuiver Q G) _ _ _ p r))
        (generatorWord Q G e) = _
      rw [ih]
      exact @Word.assoc (Paths O) (@Paths.categoryPaths O Q) G _ _ _ _ _ _ _

/-- Reading a singleton path recovers its same old segment or new letter. -/
theorem unflattenPath_single {a b : O} (e : (sumQuiver Q G).Hom a b) :
    unflattenPath Q G (@Quiver.Hom.toPath O (sumQuiver Q G) a b e) =
      generatorWord Q G e :=
  @Word.id_comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _

/-- Recover every complete normalized word from the combined free path. -/
def unflatten : Combined Q G ⥤ Relative Q G where
  obj a := ⟨a.obj⟩
  map p := unflattenPath Q G p
  map_id _ := rfl
  map_comp p q := unflattenPath_comp Q G p q

/-- The inverse keeps every complete original path as its literal old segment. -/
theorem unflatten_oldPath {a b : O} (p : @Quiver.Path O Q a b) :
    unflattenPath Q G (oldPath Q G p) =
      @Word.old (Paths O) (@Paths.categoryPaths O Q) G a b p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change unflattenPath Q G (@Quiver.Path.comp O (sumQuiver Q G) _ _ _
        (oldPath Q G p) (@Quiver.Hom.toPath O (sumQuiver Q G) _ _ (Sum.inl e))) = _
      rw [unflattenPath_comp, unflattenPath_single, ih]
      rfl

/-- Flattening recovers the original new-arrow path without changing its endpoints. -/
theorem flattenWord_generator {a b : O} (g : G a b) :
    flattenWord Q G (@RelativeWords.generator (Paths O) (@Paths.categoryPaths O Q) G a b g) =
      @Quiver.Hom.toPath O (sumQuiver Q G) a b (Sum.inr g) :=
  @eval_generator (Paths O) (@Paths.categoryPaths O Q) G (Combined Q G)
    (combinedCategory Q G) (oldNative Q G) _ a b g

/-- Reading then flattening fixes each old or new singleton path. -/
theorem flattenWord_generators {a b : O} (e : (sumQuiver Q G).Hom a b) :
    flattenWord Q G (generatorWord Q G e) =
      @Quiver.Hom.toPath O (sumQuiver Q G) a b e := by
  cases e with
  | inl e => rfl
  | inr g => exact flattenWord_generator Q G g

/-- Reading then flattening fixes every full combined path. -/
theorem flatten_unflattenPath {a b : O} (p : @Quiver.Path O (sumQuiver Q G) a b) :
    flattenWord Q G (unflattenPath Q G p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change flattenWord Q G (@Word.comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _
        (unflattenPath Q G p) (generatorWord Q G e)) = _
      rw [flattenWord_comp, ih, flattenWord_generators]
      rfl

/-- Flattening then reading fixes every full normalized relative word. -/
theorem unflatten_flattenWord {a b : O}
    (p : @Word (Paths O) (@Paths.categoryPaths O Q) G a b) :
    unflattenPath Q G (flattenWord Q G p) = p := by
  induction p with
  | old f => exact unflatten_oldPath Q G f
  | cons f g p ih =>
      change unflattenPath Q G (@Quiver.Path.comp O (sumQuiver Q G) _ _ _
        (oldPath Q G f) (@Quiver.Path.comp O (sumQuiver Q G) _ _ _
          (@Quiver.Hom.toPath O (sumQuiver Q G) _ _ (Sum.inr g)) (flattenWord Q G p))) = _
      rw [unflattenPath_comp, unflattenPath_comp, unflatten_oldPath, unflattenPath_single, ih]
      change @Word.comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _
        (@Word.old (Paths O) (@Paths.categoryPaths O Q) G _ _ f)
        (@Word.comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _
          (@RelativeWords.generator (Paths O) (@Paths.categoryPaths O Q) G _ _ g) p) = _
      exact (@Word.assoc (Paths O) (@Paths.categoryPaths O Q) G _ _ _ _ _ _ _).symm.trans
        (@cons_eq_comp (Paths O) (@Paths.categoryPaths O Q) G _ _ _ _ f g p).symm

/-- Both whole functors recover the original combined category. -/
theorem unflatten_flattenFunctor : unflatten Q G ⋙ flatten Q G = 𝟭 (Combined Q G) := by
  apply Functor.hext
  · intro a
    cases a
    rfl
  · intro a b p
    exact heq_of_eq (flatten_unflattenPath Q G p)

/-- Both whole functors recover the original relative-word category. -/
theorem flatten_unflattenFunctor : flatten Q G ⋙ unflatten Q G = 𝟭 (Relative Q G) := by
  apply Functor.hext
  · intro a
    cases a
    rfl
  · intro a b p
    exact heq_of_eq (unflatten_flattenWord Q G p)

/-- The actual relative-word category is the free category on all old and new arrows. -/
def equivalence : Relative Q G ≌ Combined Q G :=
  Equivalence.mk (flatten Q G) (unflatten Q G)
    (eqToIso (flatten_unflattenFunctor Q G).symm) (eqToIso (unflatten_flattenFunctor Q G))

end CategoryTheory.RelativeWords.FreePaths
