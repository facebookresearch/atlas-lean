/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Subdivision

/-!
# Consumers of actual barycentric subdivision

These examples exercise infinite complexes, unused ambient labels, empty
geometric complexes, repeated nerve vertices, the original vertex points, and
the distinction between vertex persistence and a simplicial map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Opposite PreAbstractSimplicialComplex
open scoped Simplicial

namespace BarycentricSubdivisionTests

private def edge : PreAbstractSimplicialComplex (Fin 2) := ⊤

private def left : Vertex edge := ⟨0, Finset.singleton_nonempty _⟩

private def right : Vertex edge := ⟨1, Finset.singleton_nonempty _⟩

private def wholeEdge : Face edge := ⟨{0, 1}, ⟨0, by simp⟩⟩

-- A genuine infinite complex has the complete comparison, with no finiteness premise.
example : Realization (subdivisionIter (⊤ : PreAbstractSimplicialComplex ℕ) 3) ≃ₜ
    Realization (⊤ : PreAbstractSimplicialComplex ℕ) := iteratedHomeomorph _ 3

-- The two original singleton faces are incomparable, so their pair is not a subdivision face.
example : ({(singletonSubdivisionVertex edge left).val,
    (singletonSubdivisionVertex edge right).val} : Finset (Face edge)) ∉
      barycentricSubdivision edge := by
  classical
  intro hs
  have hc := (mem_barycentricSubdivision edge _).mp hs
  have hcmp := hc.2.total
    (show (singletonSubdivisionVertex edge left).val ∈
      ({(singletonSubdivisionVertex edge left).val,
        (singletonSubdivisionVertex edge right).val} : Finset (Face edge)) by simp)
    (show (singletonSubdivisionVertex edge right).val ∈
      ({(singletonSubdivisionVertex edge left).val,
        (singletonSubdivisionVertex edge right).val} : Finset (Face edge)) by simp)
  rcases hcmp with h | h
  · change ({0} : Finset (Fin 2)) ⊆ {1} at h
    have bad := h (show (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) by simp)
    norm_num at bad
  · change ({1} : Finset (Fin 2)) ⊆ {0} at h
    have bad := h (show (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) by simp)
    norm_num at bad

-- The actual face vertex maps to the ordinary midpoint of the original edge.
example : (barycentricHomeomorph edge
    (Realization.vertex (barycentricSubdivision edge) wholeEdge
      (singleton_mem_orderComplex wholeEdge))).point.weights 0 = (1 : ℝ) / 2 := by
  rw [barycentricHomeomorph_point]
  simp only [Realization.vertex, Convexity.iConvexComb_single]
  rw [Realization.subBarycenter_weight_of_mem wholeEdge.val
    (edge.isRelLowerSet_faces wholeEdge.property).1 (show (0 : Fin 2) ∈ wholeEdge.val by
      simp [wholeEdge])]
  norm_num [wholeEdge]

-- Literal original points survive multiple subdivisions in both directions.
example : iteratedHomeomorph edge 4
    (Realization.vertex (subdivisionIter edge 4)
      (persistentVertex edge 4 left).val (persistentVertex edge 4 left).property) =
    Realization.vertex edge left.val left.property :=
  iteratedHomeomorph_persistentVertex edge 4 left

example : (iteratedHomeomorph edge 4).symm (Realization.vertex edge right.val right.property) =
    Realization.vertex (subdivisionIter edge 4)
      (persistentVertex edge 4 right).val (persistentVertex edge 4 right).property :=
  iteratedHomeomorph_symm_vertex edge 4 right

private def repeatedChain : (CategoryTheory.nerve (Fin 2)) _⦋2⦌ :=
  (show Fin 3 →o Fin 2 from
    { toFun := fun j => if j.val < 2 then 0 else 1
      monotone' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [Fin.le_iff_val_le_val] }).monotone.functor

private def uniformThree : Convexity.StdSimplex ℝ (Fin 3) :=
  Convexity.StdSimplex.subBarycenter Finset.univ (by simp)

private theorem uniformThree_weight (j : Fin 3) :
    uniformThree.weights j = (3 : ℝ)⁻¹ := by
  rw [uniformThree, Realization.subBarycenter_weight_of_mem _ _ (Finset.mem_univ j)]
  norm_num

-- A repeated nerve vertex contributes both weights to the actual inverse comparison.
example : ((orderComplexHomeomorph (Fin 2)).symm
    (SSet.toTop.map (SSet.yonedaEquiv.symm repeatedChain)
      ((SimplexCategory.toTopHomeo ⦋2⦌).symm uniformThree))).point.weights 0 =
      (2 : ℝ) / 3 := by
  classical
  rw [orderComplexHomeomorph_symm_cell, OrderComplex.cellCoordinates_weights_apply]
  simp only [Fin.sum_univ_succ]
  norm_num [repeatedChain]
  erw [uniformThree_weight (0 : Fin 3), uniformThree_weight (1 : Fin 3)]
  norm_num

private def ghostComplex : PreAbstractSimplicialComplex ℕ where
  faces := {s | s = {0}}
  isRelLowerSet_faces := by
    intro s hs
    change s = {0} at hs
    subst s
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    intro t ht htn
    rcases Finset.subset_singleton_iff.mp ht with hz | hz
    · exact (htn.ne_empty hz).elim
    · exact hz

private instance : Subsingleton (Face ghostComplex) where
  allEq a b := Subtype.ext (a.property.trans b.property.symm)

private def ghostVertex : Vertex ghostComplex := ⟨0, rfl⟩

-- Infinitely many ambient labels do not prevent finite actual iterates.
example (n : ℕ) : Finite (Face (subdivisionIter ghostComplex n)) :=
  finiteFaces_subdivisionIter ghostComplex n

example : (iteratedHomeomorph ghostComplex 3).symm
    (Realization.vertex ghostComplex 0 rfl) =
      Realization.vertex (subdivisionIter ghostComplex 3)
        (persistentVertex ghostComplex 3 ghostVertex).val
        (persistentVertex ghostComplex 3 ghostVertex).property :=
  iteratedHomeomorph_symm_vertex ghostComplex 3 ghostVertex

-- The affine and cardinality characteristics are available for the actual iterates.
example (s : Face (subdivisionIter edge 3)) :
    Convexity.IsAffineMap ℝ (fun q : Convexity.StdSimplex ℝ s.val =>
      (iteratedHomeomorph edge 3 (Realization.faceMap (subdivisionIter edge 3) s q)).point) :=
  isAffineMap_iteratedHomeomorph_faceMap edge 3 s

example : ∃ N : ℕ, ∀ (n : ℕ) (s : Face (subdivisionIter ghostComplex n)),
    s.val.card ≤ N + 1 := exists_uniform_subdivisionIter_card_bound ghostComplex

-- Geometrically empty complexes retain their actual empty realization and comparison.
example : IsEmpty (Realization (barycentricSubdivision (⊥ : PreAbstractSimplicialComplex ℕ))) := by
  constructor
  intro x
  obtain ⟨a, _⟩ := x.point.support_weights_nonempty
  exact a.property

example : Realization (barycentricSubdivision (⊥ : PreAbstractSimplicialComplex ℕ)) ≃ₜ
    Realization (⊥ : PreAbstractSimplicialComplex ℕ) := barycentricHomeomorph _

end BarycentricSubdivisionTests

end
