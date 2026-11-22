/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeImageMarkedIso
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Actual full supported-image cone subcomplex

The nerve of the original supported subset category is the actual
subcomplex of whole target cone simplices whose every original vertex
subset is supported in the ordinal embedding range. Both native simplex
maps and all scalar operators are retained. The marked comparison uses
literal pullback of the original maximum-preserving target marking.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Entire original target cone words supported in the exact ordinal embedding image form a genuine subcomplex. -/
def coneSupportedSubcomplex {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    (nerve (ConeSubset (f i))).Subcomplex where
  obj q := {x | ∀ t, ∀ j ∈ (x.obj t).vertices, j ∈ Set.range f}
  map g := by
    intro x hx t
    exact hx (g.unop.toOrderHom t)

/-- Every original supported target simplex lifts to the same whole simplex in the actual supported subset category. -/
def coneSupportedSimplexLift {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n)
    {q : SimplexCategoryᵒᵖ} (x : (coneSupportedSubcomplex f i).obj q) :
    (nerve (ConeEmbeddingImage f i)).obj q where
  obj t := ⟨x.val.obj t, x.property t⟩
  map h := homOfLE (leOfHom (x.val.map h))

/-- The whole nerve of supported original subsets is exactly the actual supported target cone subcomplex in
  every scalar degree. -/
def coneSupportedNerveIso {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    nerve (ConeEmbeddingImage f i) ≅ (coneSupportedSubcomplex f i : SSet.{u}) where
  hom :=
    { app q := ↾fun x => ⟨x ⋙ coneEmbeddingInclusion f i, fun t => (x.obj t).property⟩
      naturality q r g := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        rfl }
  inv :=
    { app q := ↾fun x => coneSupportedSimplexLift f i x
      naturality q r g := by
        apply ConcreteCategory.hom_ext
        intro x
        refine CategoryTheory.Functor.ext (fun t => rfl) ?_
        intro a b h
        exact Subsingleton.elim _ _ }
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun t => rfl) ?_
    intro a b h
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => rfl) ?_
    intro a b h
    exact Subsingleton.elim _ _

/-- The actual complete supported cone subcomplex carries precisely the original target maximum-preserving marks. -/
def coneSupportedMarked {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight (f i)) (coneSupportedSubcomplex f i).ι

/-- The whole supported subset-nerve comparison retains and reflects exactly every original target cone mark. -/
def coneSupportedMarkedIso {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    coneEmbeddingMarkedImage f i ≅ coneSupportedMarked f i :=
  isoMk (coneSupportedNerveIso f i) (fun _ => Iff.rfl)

/-- The complete original cone embeds as precisely its actual whole marked supported target subcomplex. -/
def coneEmbeddingSupportedIso {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m) (i : Vertex.{u} n) :
    coneWeight i ≅ coneSupportedMarked f i :=
  coneEmbeddingMarkedIso f i ≪≫ coneSupportedMarkedIso f i

end SSet.Marked.CoherentWeight
