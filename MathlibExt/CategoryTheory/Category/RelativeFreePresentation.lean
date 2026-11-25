/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsFreePaths
import MathlibExt.CategoryTheory.Category.RelativeWordHomEquivalence

/-!
# Actual free presentations retained by relative arrow attachments

A free presentation consists of an original generating quiver and a
genuine evaluation functor fixing the original labels, bijective on
every full Hom. An actual relative attachment extends that presentation
by its supplied new arrows. Complete normalized words give the proved
Hom bijections; no weak-map outcome is part of the presentation.
-/

noncomputable section
universe u v w z
open CategoryTheory

namespace CategoryTheory.RelativeWords

/-- A full free-path presentation with the same individual object labels. -/
structure FreePresentation {O : Type u} (C : Category.{v} O) where
  /-- The original generating arrow family. -/
  quiver : Quiver.{z} O
  /-- The actual interpretation of every whole original generating path. -/
  map {a b : O} : @Quiver.Path O quiver a b → @Quiver.Hom O C.toQuiver a b
  /-- The original empty path evaluates to the actual original identity. -/
  map_id (a : O) : map (@Quiver.Path.nil O quiver a) = @CategoryStruct.id O C.toCategoryStruct a
  /-- Every whole original path composition evaluates as genuine original composition. -/
  map_comp {a b c : O} (p : @Quiver.Path O quiver a b) (q : @Quiver.Path O quiver b c) :
    map (@Quiver.Path.comp O quiver a b c p q) =
      @CategoryStruct.comp O C.toCategoryStruct a b c (map p) (map q)
  /-- The original full Hom maps are genuinely bijective at each original pair. -/
  bijective (a b : O) : Function.Bijective (@map a b)

namespace FreePresentation

variable {O : Type u} {C : Category.{v} O} (P : FreePresentation.{u, v, z} C)

/-- The free presentation gives its genuine original same-label functor. -/
def functor : @Functor (Paths O) (@Paths.categoryPaths O P.quiver) O C :=
  @Functor.mk (Paths O) (@Paths.categoryPaths O P.quiver) O C
    (fun a => a) (fun {_ _} p => P.map p) P.map_id P.map_comp

/-- The original free path category has its literal full free presentation. -/
def paths (Q : Quiver.{z} O) : FreePresentation.{u,max u z,z} (@Paths.categoryPaths O Q) where
  quiver := Q
  map p := p
  map_id _ := rfl
  map_comp _ _ := rfl
  bijective _ _ := Function.bijective_id

variable (G : O → O → Type w)

/-- Interpret the complete free path on original and new arrows as its actual relative word. -/
def relativeMap {a b : O}
    (p : @Quiver.Path O (FreePaths.sumQuiver P.quiver G) a b) : @Word O C G a b :=
  @mapSameLabel (Paths O) (@Paths.categoryPaths O P.quiver) C G
    (fun {_ _} p => P.map p) P.map_id P.map_comp a b
    (FreePaths.unflattenPath P.quiver G p)

/-- The actual relative free presentation keeps the same original identity word. -/
theorem relativeMap_id (a : O) :
    relativeMap P G (@Quiver.Path.nil O (FreePaths.sumQuiver P.quiver G) a) =
      @Word.old O C G a a (@CategoryStruct.id O C.toCategoryStruct a) := by
  change @Word.old O C G a a (P.map (@Quiver.Path.nil O P.quiver a)) = _
  exact congrArg (@Word.old O C G a a) (P.map_id a)

/-- The actual full relative free-path interpretation preserves every whole composition. -/
theorem relativeMap_comp {a b c : O}
    (p : @Quiver.Path O (FreePaths.sumQuiver P.quiver G) a b)
    (q : @Quiver.Path O (FreePaths.sumQuiver P.quiver G) b c) :
    relativeMap P G (@Quiver.Path.comp O (FreePaths.sumQuiver P.quiver G) a b c p q) =
      @Word.comp O C G a b c (relativeMap P G p) (relativeMap P G q) := by
  change @mapSameLabel (Paths O) (@Paths.categoryPaths O P.quiver) C G
    (fun {_ _} p => P.map p) P.map_id P.map_comp a c
    (FreePaths.unflattenPath P.quiver G (@Quiver.Path.comp O (FreePaths.sumQuiver P.quiver
      G) a b c p q)) = _
  rw [FreePaths.unflattenPath_comp]
  exact @mapSameLabel_comp (Paths O) (@Paths.categoryPaths O P.quiver) C G
    (fun {_ _} p => P.map p) P.map_id P.map_comp a b c _ _

/-- The entire actual relative presentation is bijective on every complete original Hom. -/
theorem relativeMap_bijective (a b : O) : Function.Bijective (@relativeMap O C P G a b) := by
  have h₁ : Function.Bijective (@FreePaths.unflattenPath O P.quiver G a b) :=
    ⟨Function.LeftInverse.injective (FreePaths.flatten_unflattenPath P.quiver G),
      Function.RightInverse.surjective (FreePaths.unflatten_flattenWord P.quiver G)⟩
  have h₂ := @mapSameLabel_bijective (Paths O) (@Paths.categoryPaths O P.quiver) C G
    (fun {_ _} p => P.map p) P.map_id P.map_comp P.bijective a b
  exact h₂.comp h₁

/-- Construct the full relative free presentation from the actual original free presentation. -/
def relative : FreePresentation.{u,max u v w,max z w} (@RelativeWords.category O C G) where
  quiver := FreePaths.sumQuiver P.quiver G
  map p := relativeMap P G p
  map_id a := relativeMap_id P G a
  map_comp p q := relativeMap_comp P G p q
  bijective a b := relativeMap_bijective P G a b

/-- The extended full presentation keeps every complete original path as its actual old word. -/
theorem relativeMap_oldPath {a b : O} (p : @Quiver.Path O P.quiver a b) :
    relativeMap P G (FreePaths.oldPath P.quiver G p) = @Word.old O C G a b (P.map p) := by
  change @mapSameLabel (Paths O) (@Paths.categoryPaths O P.quiver) C G
    (fun {_ _} p => P.map p) P.map_id P.map_comp a b
    (FreePaths.unflattenPath P.quiver G (FreePaths.oldPath P.quiver G p)) = _
  rw [FreePaths.unflatten_oldPath]
  exact @mapSameLabel_old (Paths O) (@Paths.categoryPaths O P.quiver) C G
    (fun {_ _} p => P.map p) P.map_id P.map_comp a b p

/-- Every actual newly supplied generator is its same original normalized new letter. -/
theorem relativeMap_new {a b : O} (g : G a b) :
    relativeMap P G (@Quiver.Hom.toPath O (FreePaths.sumQuiver P.quiver G) a b (Sum.inr g)) =
      @RelativeWords.generator O C G a b g := by
  rw [relativeMap, FreePaths.unflattenPath_single]
  change @mapSameLabel (Paths O) (@Paths.categoryPaths O P.quiver) C G
    (fun {_ _} p => P.map p) P.map_id P.map_comp a b
    (@RelativeWords.generator (Paths O) (@Paths.categoryPaths O P.quiver) G a b g) = _
  exact @substitute_generator (Paths O) (@Paths.categoryPaths O P.quiver) G O C G
    (sameLabelFunctor (@Paths.categoryPaths O P.quiver) C
      (fun {_ _} p => P.map p) P.map_id P.map_comp) _ a b g

end FreePresentation
end CategoryTheory.RelativeWords
