/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltrationDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductUnit

/-!
# The actual free upper cell of an original coherent cone stage

The original new vertex generates the native free enriched diagram.
The preceding stage maps to this free diagram by inserting that exact
vertex, retaining all other vertices and the entire original path.
Its map to the bounded cone is the proved whole free extension, not a
chosen factorization or a projective-cofibrancy outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The native induced path morphisms are locally proof-unique without changing their original category. -/
local instance upperCellPathHomSubsingleton {n : ℕ} (i j : Vertex.{u} n)
    (p q : SimplicialThickening.Path i j) : Subsingleton (p ⟶ q) :=
  ⟨fun f g => InducedCategory.Hom.ext (Subsingleton.elim f.hom g.hom)⟩

/-- Every preceding subset supplies the strict original bound needed for insertion of the new maximum. -/
theorem coneBefore_least_lt {n : ℕ} {i k : Vertex.{u} n} (a : ConeBefore i k) : i < k :=
  (a.val.le_maximum i a.val.mem).trans_lt a.property

/-- Insert exactly the new original terminal vertex and read the resulting full coherent path. -/
def coneBeforeUpperPathFunctor {n : ℕ} (i k : Vertex.{u} n) :
    ConeBefore i k ⥤ SimplicialThickening.Path i k where
  obj a := upperConePath (coneInsertTop (coneBefore_least_lt a) a)
  map {a b} f :=
    ⟨homOfLE (show ((coneInsertTop (coneBefore_least_lt a) a).val.vertices : Set (Vertex.{u} n)) ⊆
      (coneInsertTop (coneBefore_least_lt b) b).val.vertices from
        Finset.coe_subset.mpr (Finset.insert_subset_insert k (leOfHom f)))⟩

/-- Whole original path prepending commutes with inserting only the new maximum. -/
theorem coneBeforeUpperPath_prepend {n : ℕ} {i j k : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (a : ConeBefore j k) :
    (coneBeforeUpperPathFunctor i k).obj
        ((coneBeforePrependFunctor i j k).obj (p, a)) =
      (show SimplicialThickening.mk i ⟶ SimplicialThickening.mk j from p) ≫
        (show SimplicialThickening.mk j ⟶ SimplicialThickening.mk k from
          (coneBeforeUpperPathFunctor j k).obj a) := by
  apply SimplicialThickening.Path.ext
  ext l
  change l ∈ (insert k (p.I.toFinite.toFinset ∪ a.val.vertices) : Finset (Vertex.{u} n)) ↔
    l ∈ p.I ∪ (insert k a.val.vertices : Finset (Vertex.{u} n))
  simp only [Finset.mem_insert, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union,
    Finset.mem_coe]
  tauto

/-- The actual singleton at the new original vertex is a bounded-stage object. -/
def coneUpperVertex {n : ℕ} (k : Vertex.{u} n) : ConeAtMost k k :=
  ⟨pathCone (𝟙 (SimplicialThickening.mk k)), (pathCone_maximum _).le⟩

/-- The original maximally marked point maps to the actual constant singleton cone at the new vertex. -/
def coneUpperPoint {n : ℕ} (k : Vertex.{u} n) :
    max (Δ[0] : SSet.{u}) ⟶ coneAtMostWeight k k where
  hom := SSet.const (nerveEquiv.symm (coneUpperVertex k))
  preserve _ := rfl

/-- The new upper cell is the genuine free diagram on the same original fully marked point and new vertex. -/
def coneUpperFreeDiagram {n : ℕ} (k : Vertex.{u} n) : EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk k)) (max (Δ[0] : SSet.{u}))

/-- The full free upper diagram maps to the original bounded stage by its actual original singleton extension. -/
def coneUpperFreeMap {n : ℕ} (k : Vertex.{u} n) : coneUpperFreeDiagram k ⟶ coneAtMostDiagram k :=
  enrichedFreeExtend (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk k))
    (max (Δ[0] : SSet.{u})) (coneAtMostDiagram k) (coneUpperPoint k)

/-- The preceding stage maps to the free upper cell by its whole original path and the canonical point coordinate. -/
def coneBeforeUpperFreeMap {n : ℕ} (k : Vertex.{u} n) : coneBeforeDiagram k ⟶ coneUpperFreeDiagram k where
  app i := toMax (nerveMap (coneBeforeUpperPathFunctor i.unop.as k)) ≫
    (rightPointUnitIso (max (nerve (SimplicialThickening.Path i.unop.as k)))).inv
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r z
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => ?_)
      · exact coneBeforeUpperPath_prepend _ _
      · apply InducedCategory.Hom.ext
        exact Subsingleton.elim _ _
    · apply SSet.stdSimplex.ext
      intro t
      exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

end SSet.Marked.CoherentWeight
