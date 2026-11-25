/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramAction
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# The native maximum-marked coherent cone diagram

The original endpoint-containing interval paths act contravariantly on
the marked cone subsets by whole union. Identity and composition are
the actual singleton and union laws. This supplies a genuine marked
enriched diagram on every coherent simplex, with no Kan condition on
its interval-subset Hom objects.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original coherent ordinal has exactly the original lifted vertices and interval-subset Homs. -/
abbrev Index (n : ℕ) := SimplicialThickening (Vertex.{u} n)

/-- The singleton original identity path acts as the identity on the entire cone subset. -/
theorem ConeSubset.prepend_id {n : ℕ} {i : Vertex.{u} n} (a : ConeSubset i) :
    a.prepend (𝟙 (SimplicialThickening.mk i)) = a := by
  apply ConeSubset.ext
  change ({i} : Set (Vertex.{u} n)).toFinite.toFinset ∪ a.vertices = a.vertices
  rw [Set.Finite.toFinset_singleton]
  exact Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr a.mem)

/-- Consecutive entire original paths act by the same actual coherent union composite. -/
theorem ConeSubset.prepend_comp {n : ℕ} {i j k : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (q : SimplicialThickening.Path j k) (a : ConeSubset k) :
    (a.prepend q).prepend p = a.prepend
      ((show SimplicialThickening.mk i ⟶ SimplicialThickening.mk j from p) ≫
        (show SimplicialThickening.mk j ⟶ SimplicialThickening.mk k from q)) := by
  apply ConeSubset.ext
  change p.I.toFinite.toFinset ∪ (q.I.toFinite.toFinset ∪ a.vertices) =
    (p.I ∪ q.I).toFinite.toFinset ∪ a.vertices
  rw [Set.Finite.toFinset_union]
  exact (Finset.union_assoc _ _ _).symm

/-- The maximum-marked cone weights form the genuine contravariant enriched coherent diagram. -/
def coneDiagram (n : ℕ) : EnrichedDiagram (Index.{u} n)ᵒᵖ where
  obj i := coneWeight i.unop.as
  map i j := maxCurry (coneAction j.unop.as i.unop.as)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.prepend_id _
  map_comp i j k := by
    ext q fg
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact (ConeSubset.prepend_comp _ _ _).symm

/-- The actual cone action is precisely the full native path-union marked map. -/
theorem coneDiagram_action (n : ℕ) (i j : Index.{u} n) :
    enrichedDiagramAction (coneDiagram n) (op j) (op i) = coneAction i.as j.as :=
  maxUncurry_maxCurry _

/-- Cone-diagram fibres retain the same original subset nerves and the exact maximum marking. -/
theorem coneDiagram_value (n : ℕ) (i : Index.{u} n) :
    (coneDiagram n).obj (op i) = coneWeight i.as := rfl

end SSet.Marked.CoherentWeight
