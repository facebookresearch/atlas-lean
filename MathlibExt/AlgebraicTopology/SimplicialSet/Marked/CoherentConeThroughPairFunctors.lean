/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughPair
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughFunctors

/-!
# Full original functors of ordered upper-face intersections

The first-pivot path and whole remaining second-through-cone form genuine
functors on all original subset inclusions. Native path union gives the
actual inverse functor, retaining both original pivots and every order
map. Equal pivots keep their original self-paths. This is actual source
relation geometry before any enriched colimit identification.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq
private instance {n : ℕ} (i j : Vertex.{u} n) (p q : SimplicialThickening.Path i j) : Subsingleton (p ⟶ q) :=
  ⟨fun _ _ => InducedCategory.Hom.ext (Subsingleton.elim _ _)⟩

/-- The original full two-pivot subset retains its first whole through-subset and every order map. -/
def pairFirstThroughFunctor {n : ℕ} (i j k : Vertex.{u} n) : ConeThroughPair i j k ⥤ ConeThrough i j where
  obj := pairFirstThrough
  map f := homOfLE (leOfHom f)

/-- The actual remaining second-through subset functor keeps the ordered retained pivot and whole upper cone. -/
def pairUpperThroughFunctor {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    ConeThroughPair i j k ⥤ ConeThrough j k where
  obj := pairUpperThrough hjk
  map {a b} f := homOfLE (by
    intro t ht
    obtain ⟨ht, hj⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨(leOfHom f) ht, hj⟩)

/-- Both original ordered intersection readers give the actual whole product functor. -/
def throughPairSplitFunctor {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    ConeThroughPair i j k ⥤ SimplicialThickening.Path i j × ConeThrough j k :=
  ((pairFirstThroughFunctor i j k) ⋙ throughLowerPathFunctor i j).prod' (pairUpperThroughFunctor hjk)

/-- The original full path and remaining through-cone reconstruct the complete two-pivot subset by native union. -/
def throughPairUnionFunctor {n : ℕ} (i j k : Vertex.{u} n) :
    SimplicialThickening.Path i j × ConeThrough j k ⥤ ConeThroughPair i j k where
  obj a := pathThroughPair a.1 a.2
  map {a b} f := homOfLE (by
    change a.1.I.toFinite.toFinset ∪ a.2.val.vertices ⊆ b.1.I.toFinite.toFinset ∪ b.2.val.vertices
    apply Finset.union_subset_union
    · intro t ht
      exact b.1.I.toFinite.mem_toFinset.mpr (f.1.1.1.1 (a.1.I.toFinite.mem_toFinset.mp ht))
    · exact leOfHom f.2)

/-- The complete original ordered intersection category retains its entire identity after actual splitting and union. -/
theorem throughPairSplit_union {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    throughPairSplitFunctor (i := i) hjk ⋙ throughPairUnionFunctor i j k = 𝟭 (ConeThroughPair i j k) := by
  refine CategoryTheory.Functor.ext (fun a => pathThroughPair_split hjk a) (fun _ _ _ => Subsingleton.elim _ _)

/-- Both entire original path and remaining-through categories retain their identities under native union
  and splitting. -/
theorem throughPairUnion_split {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    throughPairUnionFunctor i j k ⋙ throughPairSplitFunctor (i := i) hjk =
      𝟭 (SimplicialThickening.Path i j × ConeThrough j k) := by
  refine CategoryTheory.Functor.ext
    (fun a => Prod.ext (pairFirstThrough_lower_path a.1 a.2) (pairUpperThrough_path hjk a.1 a.2)) ?_
  intro a b f
  exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end SSet.Marked.CoherentWeight
