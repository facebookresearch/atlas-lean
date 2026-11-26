/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.MaximalIndependentSets
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- An edgeless graph has a unique maximal independent set, even when it has no vertices.
example (V : Type*) [Fintype V] : maxIndepSetCount (⊥ : SimpleGraph V) = 1 := by
  apply Set.ncard_eq_one.mpr
  refine ⟨Set.univ, ?_⟩
  ext I
  change Maximal (⊥ : SimpleGraph V).IsIndepSet I ↔ I = Set.univ
  have hi : (⊥ : SimpleGraph V).IsIndepSet Set.univ := by
    simp [SimpleGraph.isIndepSet_iff, Set.Pairwise]
  constructor
  · intro h
    exact Set.eq_univ_of_univ_subset (h.2 hi (Set.subset_univ I))
  · rintro rfl
    exact ⟨hi, fun _ _ _ ↦ Set.subset_univ _⟩

-- On the empty graph the degree-zero convention makes the upper bound exactly one.
example : (maxIndepSetCount (⊥ : SimpleGraph (Fin 0)) : ℝ) ≤ 1 := by
  simpa using maxIndepSetCount_le_of_maxDegree_le (⊥ : SimpleGraph (Fin 0))
    (k := 1) le_rfl (by simp)

-- On a single edge both degrees are one and every binomial coefficient is included.
example : (maxIndepSetCount (⊤ : SimpleGraph (Fin 2)) : ℝ) ≤ 4 * (3 : ℝ) ^ (5 / 3 : ℝ) := by
  have h := maxIndepSetCount_le_of_maxDegree_le (⊤ : SimpleGraph (Fin 2)) (k := 1) le_rfl
    (by simp [SimpleGraph.maxDegree_top, SimpleGraph.minDegree_top])
  norm_num [SimpleGraph.minDegree_top, Finset.sum_range_succ, Nat.choose] at h ⊢
  exact h

-- A single edge has excess −1. Its sign increases the exponent by 1/13.
example : (maxIndepSetCount (⊤ : SimpleGraph (Fin 2)) : ℝ) ≤ (3 : ℝ) ^ (32 / 39 : ℝ) := by
  have h := maxIndepSetCount_le_of_edge_count (⊤ : SimpleGraph (Fin 2)) (-1) (Δ := 1)
    le_rfl (by simp [SimpleGraph.maxDegree_top])
    (by rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]; decide)
  rw [← Real.rpow_add (by norm_num)] at h
  norm_num at h ⊢
  exact h

-- Five disjoint copies of K₄ have 20 vertices, 30 edges and maximum degree three.
-- The edge correction outweighs the prefactor, improving the exponent 20/3 by 1/39.
example : (maxIndepSetCount ((⊥ : SimpleGraph (Fin 5)) □ (⊤ : SimpleGraph (Fin 4))) : ℝ) ≤
    (3 : ℝ) ^ (20 / 3 - 1 / 39 : ℝ) := by
  classical
  let G := (⊥ : SimpleGraph (Fin 5)) □ (⊤ : SimpleGraph (Fin 4))
  let : G.LocallyFinite := fun v ↦ Subtype.fintype (· ∈ G.neighborSet v)
  have hd : G.IsRegularOfDegree 3 := by
    intro v
    rw [SimpleGraph.degree_boxProd, SimpleGraph.bot_degree, zero_add]
    exact SimpleGraph.complete_graph_degree (V := Fin 4) v.2
  have he := G.sum_degrees_eq_twice_card_edges
  simp [hd.degree_eq] at he
  have h := maxIndepSetCount_le_of_edge_count G 10 (Δ := 3) (by decide) hd.maxDegree_eq (by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega)
  rw [← Real.rpow_add (by norm_num)] at h
  norm_num at h ⊢
  exact h

-- With no deleted vertices the almost triangle-free bound is the triangle-free bound.
example {V : Type*} [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    {D : ℕ} (hD : 1 ≤ D) (hV : 1 ≤ Fintype.card V) (k : ℝ)
    (htri : ∀ a b c : V, ¬(Γ.Adj a b ∧ Γ.Adj b c ∧ Γ.Adj a c))
    (hΔ : Γ.maxDegree ≤ D) (he : (Fintype.card V : ℝ) / 2 + k ≤ Γ.edgeSet.ncard) :
    (maxIndepSetCount Γ : ℝ) ≤
      (2 : ℝ) ^ ((Fintype.card V : ℝ) / 2 - k / (100 * (D : ℝ) ^ 2)) := by
  classical
  simpa using maxIndepSetCount_le_of_almost_triangleFree Γ ∅ hV hD k
    (fun a b c _ _ _ ↦ htri a b c) hΔ (by simp) (by simpa using he)

example : (maxIndepSetCount (⊥ : SimpleGraph (Fin 1)) : ℝ) ≤
    (2 : ℝ) ^ (101 / 200 : ℝ) := by
  have h := maxIndepSetCount_le_of_almost_triangleFree (⊥ : SimpleGraph (Fin 1)) ∅
    (n := 1) (D := 1) (by decide) (by decide) (-1 / 2)
    (by simp) (by simp) (by simp) (by norm_num)
  norm_num at h ⊢
  exact h

example : (maxIndepSetCount (⊥ : SimpleGraph (Fin 2)) : ℝ) ≤
    (2 : ℝ) ^ (501 / 200 : ℝ) := by
  have h := maxIndepSetCount_le_of_almost_triangleFree (⊥ : SimpleGraph (Fin 2)) {0}
    (n := 1) (D := 1) (by decide) (by decide) (-1 / 2)
    (by simp) (by simp) (by simp) (by norm_num)
  norm_num at h ⊢
  exact h

private def pentagon : SimpleGraph (Fin 5) where
  Adj a b := (a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel pentagon.Adj := by
  unfold pentagon
  infer_instance

example : (maxIndepSetCount pentagon : ℝ) ≤ (2 : ℝ) ^ (399 / 160 : ℝ) := by
  have he : pentagon.edgeSet.ncard = 5 := by
    rw [← pentagon.coe_edgeFinset, Set.ncard_coe_finset]
    decide
  have h := maxIndepSetCount_le_of_almost_triangleFree pentagon ∅
    (n := 5) (D := 2) (by decide) (by decide) (5 / 2)
    (by decide) (by decide) (by simp) (by simpa using he.ge)
  norm_num at h ⊢
  exact h

#check @MetaMathlibExt.maxIndepSetCount_le_of_almost_triangleFree
#print axioms MetaMathlibExt.maxIndepSetCount_le_of_almost_triangleFree
