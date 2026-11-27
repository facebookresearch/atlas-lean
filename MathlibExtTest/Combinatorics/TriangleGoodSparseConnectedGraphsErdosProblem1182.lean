/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.TriangleGoodSparseConnectedGraphsErdosProblem1182
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Push

open Filter MathlibExt.Combinatorics.TriangleGoodSparseConnectedGraphsErdosProblem1182Wanted

-- The refutation, as stated.
example : ¬ triangleGoodnessSuperlinearThreshold :=
  triangleGoodnessSuperlinearThreshold_refuted

-- The equivalent form in the docstring: for one constant `C` and infinitely many `n`, some
-- connected graph on `n` vertices with at most `C n` edges has `R(K₃, G) ≠ 2 n - 1`.
example : ∃ C : ℝ, ∃ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n), G.Connected ∧
    (G.edgeSet.ncard : ℝ) ≤ C * n ∧
    SimpleGraph.graphPairRamsey (⊤ : SimpleGraph (Fin 3)) G ≠ 2 * n - 1 := by
  have h := triangleGoodnessSuperlinearThreshold_refuted
  unfold triangleGoodnessSuperlinearThreshold at h
  push Not at h
  exact h

-- The value `2 n - 1` in the statement is attained: a single edge is connected, and
-- `R(K₃, K₂) = 3`.
example : (⊤ : SimpleGraph (Fin 2)).Connected ∧
    SimpleGraph.graphPairRamsey (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 2)) =
      2 * 2 - 1 := by
  refine ⟨SimpleGraph.connected_top, ?_⟩
  rw [SimpleGraph.graphPairRamsey_eq_sInf]
  -- every graph on three vertices is a triangle or misses an edge
  have h3 : ∀ C : SimpleGraph (Fin 3),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ (⊤ : SimpleGraph (Fin 2)).IsContained Cᶜ := by
    intro C
    by_cases hC : Cᶜ = ⊥
    · left
      rw [compl_eq_bot] at hC
      subst hC
      exact ⟨SimpleGraph.Copy.id _⟩
    · right
      exact (SimpleGraph.not_cliqueFree_iff_top_isContained 2).1
        (by rwa [SimpleGraph.cliqueFree_two])
  refine le_antisymm (Nat.sInf_le h3) (le_csInf ⟨3, h3⟩ fun N hN => ?_)
  -- on fewer than three vertices, the complete graph has no triangle and its complement no edge
  by_contra hlt
  rcases hN ⊤ with h | h
  · obtain ⟨φ⟩ := h
    have := Fintype.card_le_of_injective _ φ.injective
    simp only [Fintype.card_fin] at this
    omega
  · obtain ⟨φ⟩ := h
    have := φ.toHom.map_adj (show (⊤ : SimpleGraph (Fin 2)).Adj 0 1 by decide)
    simp at this
