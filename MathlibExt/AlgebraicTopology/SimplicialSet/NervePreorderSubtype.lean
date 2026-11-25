/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Whole nerves of original preorder subtypes

The nerve of the actual subtype of a preorder is exactly the subcomplex
of its original nerve whose every scalar vertex satisfies the supplied
predicate. Both whole simplex maps keep all original order morphisms,
faces and degeneracies. This is a strict original-carrier comparison;
no categorical equivalence or model outcome is supplied.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet
variable {C : Type u} [Preorder C]

/-- Entire original preorder nerve words whose every scalar vertex satisfies the predicate form the actual
  subtype subcomplex. -/
def preorderSubtypeSubcomplex (P : C → Prop) : (nerve C).Subcomplex where
  obj q := {x | ∀ t, P (x.obj t)}
  map f := by
    intro x hx t
    exact hx (f.unop.toOrderHom t)

/-- The original subtype preorder includes by its whole original order map. -/
def preorderSubtypeInclusion (P : C → Prop) : {x : C // P x} ⥤ C where
  obj := Subtype.val
  map h := homOfLE (leOfHom h)

/-- Every original predicate-supported simplex lifts to its actual whole subtype simplex. -/
def preorderSubtypeSimplexLift (P : C → Prop) {q : SimplexCategoryᵒᵖ}
    (x : (preorderSubtypeSubcomplex P).obj q) : (nerve {a : C // P a}).obj q where
  obj t := ⟨x.val.obj t, x.property t⟩
  map h := homOfLE (leOfHom (x.val.map h))

/-- The original preorder subtype nerve is exactly its whole predicate-supported nerve subcomplex,
  preserving every original scalar operator. -/
def nervePreorderSubtypeIso (P : C → Prop) : nerve {x : C // P x} ≅ (preorderSubtypeSubcomplex P : SSet.{u}) where
  hom :=
    { app q := ↾fun x => ⟨x ⋙ preorderSubtypeInclusion P, fun t => (x.obj t).property⟩
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        rfl }
  inv :=
    { app q := ↾fun x => preorderSubtypeSimplexLift P x
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro x
        refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _) }
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

end SSet
