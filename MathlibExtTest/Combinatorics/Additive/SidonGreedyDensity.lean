/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.Combinatorics.Additive.SidonGreedyDensity

open MetaMathlibExt

-- The construction starts at 1, not 0.
example : (0 : ℕ) ∉ greedySidon := by
  intro h
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
  exact Nat.not_succ_le_zero 0 (greedyPrefix_subset_Icc n hn).1

private theorem greedyPrefix_one : greedyPrefix 1 = {1} := by
  ext x
  simp [greedyPrefix, Set.IsSidon]

-- The first interval has exactly one point of the infinite Sidon set.
example : (greedySidon ∩ Set.Icc 1 1).ncard = 1 := by
  rw [greedySidon_inter_Icc, Set.ncard_coe_finset, greedyPrefix_one, Finset.card_singleton]

-- The algorithm keeps 2, but rejects 3 because 3 + 1 = 2 + 2.
example : greedyPrefix 3 = {1, 2} := by
  have h2 : (insert 2 ({1} : Set ℕ)).IsSidon := by
    intro a ha b hb c hc d hd h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
    omega
  have hprefix : greedyPrefix 2 = {1, 2} := by
    rw [show (2 : ℕ) = 1 + 1 by decide, greedyPrefix, greedyPrefix_one]
    rw [ite_eq_left (by simpa using h2)]
    ext x
    simp [or_comm]
  have h3 : ¬ (insert 3 (greedyPrefix 2 : Set ℕ)).IsSidon := by
    intro h
    rw [hprefix] at h
    have hcollision := h 3 (by simp) 1 (by simp) 2 (by simp) 2 (by simp) (by decide)
    omega
  change greedyPrefix (2 + 1) = {1, 2}
  rw [greedyPrefix, ite_eq_right h3, hprefix]
