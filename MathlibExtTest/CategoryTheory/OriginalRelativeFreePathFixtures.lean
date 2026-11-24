/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsFreePaths
import MathlibExt.CategoryTheory.Category.RelativeFreePresentation
import MathlibExt.CategoryTheory.Category.FixedLabelPathFilteredColimit

/-!
# Original relative free-path clients with loops and independent universes

The full old and new arrow families keep independent universes and the
same original labels. Distinct supplied loop arrows remain distinct after
whole relative-word readback and flattening. Empty original labels retain
no objects, while all original full inverse functor equations are consumed.
-/

universe u v w
open CategoryTheory
namespace CategoryTheory.OriginalRelativeFreePathFixtures
open RelativeWords

/-- The original full inverse functors are usable with independent original label and arrow universes. -/
theorem independent_whole_inverses {O : Type (u+17)} (Q : Quiver.{v+19} O)
    (G : O → O → Type (w+23)) :
    FreePaths.flatten Q G ⋙ FreePaths.unflatten Q G = 𝟭 (FreePaths.Relative Q G) ∧
      FreePaths.unflatten Q G ⋙ FreePaths.flatten Q G = 𝟭 (FreePaths.Combined Q G) :=
  ⟨FreePaths.flatten_unflattenFunctor Q G, FreePaths.unflatten_flattenFunctor Q G⟩

/-- One original object with one old generator and two separately supplied new loops. -/
@[instance_reducible]
def loopQuiver : Quiver.{u} (ULift.{u} PUnit.{1}) where
  Hom _ _ := PUnit.{u+1}

/-- The SAME original individual loop object. -/
def loopVertex : ULift.{u} PUnit.{1} := ⟨PUnit.unit⟩

/-- The new loop family retains both distinct actual original labels. -/
def newLoops : ULift.{u} PUnit.{1} → ULift.{u} PUnit.{1} → Type u := fun _ _ => ULift.{u} Bool

/-- Two genuinely distinct new loops remain distinct whole native paths after flattening. -/
theorem distinct_new_loops :
    FreePaths.flattenWord loopQuiver.{u} newLoops
        (@RelativeWords.generator (Paths (ULift.{u} PUnit.{1}))
          (@Paths.categoryPaths (ULift.{u} PUnit.{1}) loopQuiver) newLoops loopVertex loopVertex ⟨false⟩) ≠
      FreePaths.flattenWord loopQuiver newLoops
        (@RelativeWords.generator (Paths (ULift.{u} PUnit.{1}))
          (@Paths.categoryPaths (ULift.{u} PUnit.{1}) loopQuiver) newLoops loopVertex loopVertex ⟨true⟩) := by
  intro h
  have h0 := FreePaths.flattenWord_generator loopQuiver.{u} newLoops (a := loopVertex) (b := loopVertex) ⟨false⟩
  have h1 := FreePaths.flattenWord_generator loopQuiver.{u} newLoops (a := loopVertex) (b := loopVertex) ⟨true⟩
  have h' := h0.symm.trans (h.trans h1)
  have he := @Quiver.Path.hom_heq_of_cons_eq_cons (ULift.{u} PUnit.{1})
    (FreePaths.sumQuiver loopQuiver newLoops) _ _ _ _ _ _ _ _ h'
  have hx : (Sum.inr (ULift.up false) : loopQuiver.Hom loopVertex loopVertex ⊕ newLoops loopVertex loopVertex) =
      Sum.inr (ULift.up true) := eq_of_heq he
  exact Bool.false_ne_true (congrArg ULift.down (Sum.inr.inj hx))

/-- Every full original empty-labelled relative path category retains no objects. -/
theorem empty_relative_no_objects (Q : Quiver.{v} PEmpty.{u+1})
    (G : PEmpty.{u+1} → PEmpty.{u+1} → Type w) :
    IsEmpty (FreePaths.Relative Q G) ∧ IsEmpty (FreePaths.Combined Q G) :=
  ⟨⟨fun x => PEmpty.elim x.obj⟩, ⟨fun x => PEmpty.elim x.obj⟩⟩

end CategoryTheory.OriginalRelativeFreePathFixtures
