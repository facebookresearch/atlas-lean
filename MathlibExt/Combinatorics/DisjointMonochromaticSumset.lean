/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.PairwiseSumTheorem
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Disjoint infinite sets with monochromatic union and sumset

Splitting an infinite witness to the pairwise sum theorem into two disjoint infinite sets
gives a single color for both sets and every sum across them.
-/

namespace MetaMathlibExt

/-- **Disjoint infinite sets with monochromatic union and sumset.** For every finite coloring of
$\mathbb{N} = \{0, 1, 2, \dots\}$ there are disjoint infinite sets $A, B \subseteq \mathbb{N}$ such
that $A \cup B \cup (A + B)$ is monochromatic, where $A + B = \{a + b : a \in A, b \in B\}$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 2.2 (`integers-2025-A105-thm-2-2`). -/
public theorem exists_disjoint_infinite_union_add_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ Disjoint A B ∧ ∃ k : Fin r,
      (∀ a ∈ A, c a = k) ∧ (∀ b ∈ B, c b = k) ∧ ∀ a ∈ A, ∀ b ∈ B, c (a + b) = k := by
  obtain ⟨S, hS, k, hmem, hsum⟩ := exists_infinite_pairwiseSums_monochromatic c
  obtain ⟨A, B, rfl, hdisj, hcard⟩ := hS.exists_union_disjoint_cardinal_eq_of_infinite
  have hinf : A.Infinite ↔ B.Infinite := by
    rw [← Cardinal.aleph0_le_mk_set, ← Cardinal.aleph0_le_mk_set, hcard]
  have hB : B.Infinite := (Set.infinite_union.mp hS).elim hinf.mp id
  exact ⟨A, B, hinf.mpr hB, hB, hdisj, k, fun a ha => hmem a (Or.inl ha),
    fun b hb => hmem b (Or.inr hb),
    fun a ha b hb => hsum a (Or.inl ha) b (Or.inr hb) (hdisj.ne_of_mem ha hb)⟩

end MetaMathlibExt
