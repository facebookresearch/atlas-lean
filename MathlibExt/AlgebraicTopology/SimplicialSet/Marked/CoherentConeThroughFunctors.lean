/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughSplit

/-!
# Actual full functors of the original through-subset split

The lower-path and upper-cone readers preserve every original subset
inclusion. Whole path union reconstructs their genuine product functor.
Both entire functor inverse equations retain the original order maps;
no equivalence of a model or a chosen chart is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

private instance {n : ℕ} (i j : Vertex.{u} n) (p q : SimplicialThickening.Path i j) : Subsingleton (p ⟶ q) :=
  ⟨fun _ _ => InducedCategory.Hom.ext (Subsingleton.elim _ _)⟩

/-- Every original through-subset inclusion retains its entire lower coherent path. -/
def throughLowerPathFunctor {n : ℕ} (i j : Vertex.{u} n) : ConeThrough i j ⥤ SimplicialThickening.Path i j where
  obj := throughLowerPath
  map {a b} f := ⟨homOfLE (show (throughLowerPath a).I ⊆ (throughLowerPath b).I from
    fun t ht => ⟨(leOfHom f) ht.1, ht.2⟩)⟩

/-- Every original through-subset inclusion retains its entire upper cone. -/
def throughUpperConeFunctor {n : ℕ} (i j : Vertex.{u} n) : ConeThrough i j ⥤ ConeSubset j where
  obj := throughUpperCone
  map {a b} f := homOfLE (by
    intro t ht
    obtain ⟨ht, hj⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨(leOfHom f) ht, hj⟩)

/-- The original full split is the genuine product functor on both native readers. -/
def throughSplitFunctor {n : ℕ} (i j : Vertex.{u} n) :
    ConeThrough i j ⥤ SimplicialThickening.Path i j × ConeSubset j :=
  (throughLowerPathFunctor i j).prod' (throughUpperConeFunctor i j)

/-- The entire original product path and upper cone reconstruct by their actual native whole union. -/
def throughUnionFunctor {n : ℕ} (i j : Vertex.{u} n) :
    SimplicialThickening.Path i j × ConeSubset j ⥤ ConeThrough i j where
  obj a := pathThrough a.1 a.2
  map {a b} f := homOfLE (by
    change a.1.I.toFinite.toFinset ∪ a.2.vertices ⊆ b.1.I.toFinite.toFinset ∪ b.2.vertices
    apply Finset.union_subset_union
    · intro t ht
      exact b.1.I.toFinite.mem_toFinset.mpr (f.1.1.1.1 (a.1.I.toFinite.mem_toFinset.mp ht))
    · exact leOfHom f.2)

/-- Original whole splitting then union retains the identity of the complete through-subset category. -/
theorem throughSplit_union {n : ℕ} (i j : Vertex.{u} n) :
    throughSplitFunctor i j ⋙ throughUnionFunctor i j = 𝟭 (ConeThrough i j) := by
  refine CategoryTheory.Functor.ext (fun a => pathThrough_split a) ?_
  intro a b f
  exact Subsingleton.elim _ _

/-- Original whole union then splitting retains the identity of both original path and upper-cone categories. -/
theorem throughUnion_split {n : ℕ} (i j : Vertex.{u} n) :
    throughUnionFunctor i j ⋙ throughSplitFunctor i j = 𝟭 (SimplicialThickening.Path i j × ConeSubset j) := by
  refine CategoryTheory.Functor.ext
    (fun a => Prod.ext (throughLowerPath_pathThrough a.1 a.2) (throughUpperCone_pathThrough a.1 a.2)) ?_
  intro a b f
  exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end SSet.Marked.CoherentWeight
