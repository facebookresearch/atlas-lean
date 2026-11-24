/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.MonochromaticCliquePartitionLeftover

namespace MathlibExtTest.Combinatorics.SimpleGraph.MonochromaticCliquePartitionLeftover

open _root_.SimpleGraph Finset
open MathlibExt.Combinatorics.MonochromaticCliquePartitionLeftoverErdosProblem1015Wanted

private def redPair : Finset (Fin 4) := {0, 1}
private def bluePair : Finset (Fin 4) := {2, 3}

example : IsMonochromaticCliquePacking (edge (0 : Fin 4) 1) 2 {redPair, bluePair} := by
  have hd : Disjoint redPair bluePair := by decide
  refine ⟨?_, ?_⟩
  · intro A hA B hB hAB
    simp only [mem_coe, mem_insert, mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hAB rfl).elim
  · intro S hS
    rcases mem_insert.1 hS with rfl | hS
    · exact Or.inl (by simp [redPair, isNClique_iff, edge_adj])
    · rw [mem_singleton.1 hS]
      right
      simp only [bluePair, isNClique_iff, coe_insert, coe_singleton, isClique_pair, compl_adj,
        edge_adj]
      decide

example : ¬ IsMonochromaticCliquePacking (⊤ : SimpleGraph (Fin 3)) 2 {{0, 1}, {1, 2}} := by
  intro hP
  have h₁ : ({0, 1} : Finset (Fin 3)) ∈ ({ {0, 1}, {1, 2} } : Finset _) := by simp
  have h₂ : ({1, 2} : Finset (Fin 3)) ∈ ({ {0, 1}, {1, 2} } : Finset _) := by simp
  have hne : ({0, 1} : Finset (Fin 3)) ≠ {1, 2} := by decide
  have hd := hP.1 h₁ h₂ hne
  exact Finset.disjoint_left.1 hd (by simp : (1 : Fin 3) ∈ ({0, 1} : Finset _)) (by simp)

private theorem ramsey_two_one : graphRamsey 2 1 = 1 := by
  have hone : classicalRamsey 2 1 1 := by
    intro G
    have h : Gᶜ.IsNClique 1 ({0} : Finset (Fin 1)) := by simp [isNClique_singleton]
    exact Or.inr ((not_cliqueFree_iff_top_isContained 1).1 h.not_cliqueFree)
  have hle : graphRamsey 2 1 ≤ 1 := Nat.sInf_le (s := {N | classicalRamsey 2 1 N}) hone
  by_contra he
  have hzero : graphRamsey 2 1 = 0 := by omega
  have h : classicalRamsey 2 1 (graphRamsey 2 1) :=
    Nat.sInf_mem (s := {N | classicalRamsey 2 1 N}) ⟨1, hone⟩
  rw [hzero] at h
  rcases h ⊥ with h | h
  · exact Fin.elim0 (h.some 0)
  · exact Fin.elim0 (h.some 0)

example (n : ℕ) : leftoverValue 2 n = n % 2 := by
  simp [leftoverValue, ramsey_two_one]

example : ∃ n₀ : ℕ, ∀ n ≥ n₀, n % 2 = 0 → ∀ G : SimpleGraph (Fin n),
    ∃ P, IsMonochromaticCliquePacking G 2 P ∧ n - 2 * P.card = 0 := by
  obtain ⟨n₀, hn₀⟩ := monochromaticCliquePartitionLeftover_holds 2 (by decide)
  refine ⟨n₀, fun n hn he G => ?_⟩
  obtain ⟨P, hP, hb⟩ := (hn₀ n hn).1 G
  rw [show leftoverValue 2 n = 0 by simp [leftoverValue, ramsey_two_one, he]] at hb
  exact ⟨P, hP, Nat.eq_zero_of_le_zero hb⟩

end MathlibExtTest.Combinatorics.SimpleGraph.MonochromaticCliquePartitionLeftover
