/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EpsilonLightSubset
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.EpsilonLightSubset` -/

namespace MathlibExtTest.EpsilonLightSubset

open Matrix SimpleGraph MathlibExt.Combinatorics.EpsilonLightSubsetWanted

/-- The Laplacian matrix of a graph without edges vanishes. -/
private lemma lapMatrix_eq_zero_of_forall_not_adj {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (inst : DecidableRel H.Adj) (h : ∀ a b, ¬ H.Adj a b) :
    @lapMatrix V ℝ _ H inst _ _ = 0 := by
  ext i j
  have hdeg : H.degree i = 0 := by
    rw [degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    exact h i w ((mem_neighborFinset H i w).mp hw)
  simp [lapMatrix, degMatrix, adjMatrix, hdeg, h, diagonal]

-- Test section: the definition. In a graph without edges every vertex set is `0`-light.
example (S : Finset (Fin 3)) : IsEpsilonLight (⊥ : SimpleGraph (Fin 3)) 0 S := by
  classical
  unfold IsEpsilonLight
  rw [lapMatrix_eq_zero_of_forall_not_adj, lapMatrix_eq_zero_of_forall_not_adj]
  · simpa using PosSemidef.zero
  · simp
  · simp

-- A single vertex is `ε`-light for every `ε ≥ 0`, in any graph.
example (G : SimpleGraph (Fin 4)) (ε : ℝ) (hε : 0 ≤ ε) : IsEpsilonLight G ε {0} := by
  classical
  unfold IsEpsilonLight
  rw [lapMatrix_eq_zero_of_forall_not_adj (G.induce _).spanningCoe, sub_zero]
  · exact (posSemidef_lapMatrix ℝ G).smul hε
  · simp only [map_adj, comap_adj, not_exists, not_and]
    intro a b x y hxy _ _
    have hx : (x : Fin 4) = 0 := by simpa using x.2
    have hy : (y : Fin 4) = 0 := by simpa using y.2
    simp only [Function.Embedding.subtype_apply, hx, hy] at hxy
    exact G.irrefl hxy

-- A set containing an edge is not `0`-light: in the complete graph on two vertices, the whole
-- vertex set is not even `1/2`-light, as the vector `(1, -1)` shows.
example : ¬ IsEpsilonLight (⊤ : SimpleGraph (Fin 2)) (1 / 2) Finset.univ := by
  classical
  unfold IsEpsilonLight
  intro h
  have := h.dotProduct_mulVec_nonneg ![1, -1]
  rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
    ← toLinearMap₂'_apply', ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂',
    lapMatrix_toLinearMap₂'] at this
  simp [Fin.sum_univ_two] at this
  norm_num at this

-- Test section: the theorem. For the complete graph on `100` vertices, the theorem gives
-- `ε`-light sets of size proportional to `ε`.
example : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ S : Finset (Fin 100),
    IsEpsilonLight (⊤ : SimpleGraph (Fin 100)) ε S ∧ c * ε * 100 ≤ S.card := by
  obtain ⟨c, hc, h⟩ := epsilonLightSubsetExists_holds
  refine ⟨c, hc, fun ε hε hε1 => ?_⟩
  obtain ⟨S, hS, hcard⟩ := h 100 ⊤ ε hε hε1
  exact ⟨S, hS, by exact_mod_cast hcard⟩

end MathlibExtTest.EpsilonLightSubset
