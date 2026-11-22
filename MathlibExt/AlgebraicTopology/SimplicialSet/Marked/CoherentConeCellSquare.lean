/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeStageCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedTopMarkedPushout

/-!
# The whole original cone-stage attachment square

The native preceding-stage top endpoint agrees with its original free
upper-cell attachment. The full free map is the original coherent path
followed by its actual endpoint-containing cone inclusion. All these
equations are equations of whole enriched marked maps, retaining every
original Hom parameter and scalar operator.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The bounded-stage action is exactly its same entire original path-union map. -/
theorem coneAtMostDiagram_action {n : ℕ} (k : Vertex.{u} n) (i j : Index.{u} n) :
    enrichedDiagramAction (coneAtMostDiagram k) (op j) (op i) = coneAtMostAction i.as j.as k :=
  maxUncurry_maxCurry _

/-- Prepending a whole original path to its actual terminal singleton recovers that exact
  endpoint-containing path subset. -/
theorem coneUpperVertex_prepend {n : ℕ} {i k : Vertex.{u} n} (p : SimplicialThickening.Path i k) :
    (coneUpperVertex k).val.prepend p = pathCone p := by
  apply ConeSubset.ext
  change p.I.toFinite.toFinset ∪ ({k} : Set (Vertex.{u} n)).toFinite.toFinset = p.I.toFinite.toFinset
  rw [Set.Finite.toFinset_singleton]
  exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (p.I.toFinite.mem_toFinset.mpr p.right))

/-- The entire original coherent path includes into the bounded stage by its original endpoint-containing subset. -/
def coneUpperPathFunctor {n : ℕ} (i k : Vertex.{u} n) :
    SimplicialThickening.Path i k ⥤ ConeAtMost i k :=
  pathUpperConeFunctor i k ⋙
    { obj a := ⟨a.val, a.property.le⟩
      map f := homOfLE (leOfHom f) }

/-- Every original coherent Hom edge is marked in its actual upper-layer inclusion because the same maximum
  is retained. -/
def coneUpperPathMap {n : ℕ} (i k : Vertex.{u} n) :
    max (nerve (SimplicialThickening.Path i k)) ⟶ coneAtMostWeight i k where
  hom := nerveMap (coneUpperPathFunctor i k)
  preserve {e} _ := (pathCone_maximum (e.obj 0)).trans (pathCone_maximum (e.obj 1)).symm

/-- The genuine free upper-cell extension is exactly the whole original coherent Hom inclusion, with only
  its canonical point coordinate projected away. -/
theorem coneUpperFreeMap_component {n : ℕ} (k : Vertex.{u} n) (i : Index.{u} n) :
    (coneUpperFreeMap k).app (op i) =
      prodFst (max (nerve (SimplicialThickening.Path i.as k))) (max (Δ[0] : SSet.{u})) ≫
        coneUpperPathMap i.as k := by
  change prodMap (𝟙 _) (coneUpperPoint k) ≫
    enrichedDiagramAction (coneAtMostDiagram k) (op (SimplicialThickening.mk k)) (op i) = _
  rw [coneAtMostDiagram_action]
  apply Hom.ext
  ext q z
  refine CategoryTheory.Functor.ext (fun t => Subtype.ext ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact coneUpperVertex_prepend _

/-- The entire original top-interval attachment is the same whole enriched square as the free new-vertex attachment. -/
theorem coneStageCell_condition {n : ℕ} (k : Vertex.{u} n) :
    enrichedDiagramCylinderTop (coneBeforeDiagram k) ≫ coneBeforeStagePrismMap k =
      coneBeforeUpperFreeMap k ≫ coneUpperFreeMap k := by
  apply EnrichedDiagramMap.ext
  funext i
  change (enrichedDiagramCylinderTop (coneBeforeDiagram k)).app i ≫
    coneBeforeStagePrism i.unop.as k =
      (coneBeforeUpperFreeMap k).app i ≫ (coneUpperFreeMap k).app i
  rw [coneUpperFreeMap_component k i.unop]
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun t => Subtype.ext ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact (congrArg Subtype.val (pathUpperCone_upperConePath
    (coneInsertTop (coneBefore_least_lt (a.obj t)) (a.obj t)))).symm

end SSet.Marked.CoherentWeight
