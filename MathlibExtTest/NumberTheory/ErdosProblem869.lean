/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem869

open MathlibExt.NumberTheory.ErdosProblem869Wanted

-- The negation gives two bases for which even a minimal basis using both colours is impossible.
example : ∃ A B : Set ℕ, Disjoint A B ∧ IsAdditiveBasisOrder2 A ∧ IsAdditiveBasisOrder2 B ∧
    ∀ D ⊆ A ∪ B, ¬ IsMinimalAdditiveBasisOrder2 D := by
  classical
  by_contra! h
  apply Statement_refuted
  intro A B hd ha hb
  exact h A B hd ha hb

-- A singleton represents just its doubled element, including when that element is zero.
example (a : ℕ) : addSumset {a} = {a + a} := by
  ext n
  simp [addSumset, eq_comm]

-- A basis may miss an initial interval. Even its least element can be removed in this example.
example (k : ℕ) : IsAdditiveBasisOrder2 (Set.Ici k) ∧
    ¬ IsMinimalAdditiveBasisOrder2 (Set.Ici k) := by
  constructor
  · refine ⟨2 * k, fun n hn => ⟨k, Set.mem_Ici.mpr le_rfl, n - k, ?_, by omega⟩⟩
    change k ≤ n - k
    omega
  · intro h
    apply h.2 k (Set.mem_Ici.mpr le_rfl)
    refine (Set.finite_lt_nat (2 * (k + 1))).subset ?_
    intro n hn
    change n < 2 * (k + 1)
    by_contra! hle
    apply hn
    exact ⟨k + 1, ⟨by change k ≤ k + 1; omega, by change k + 1 ≠ k; omega⟩,
      n - (k + 1), ⟨by change k ≤ n - (k + 1); omega, by change n - (k + 1) ≠ k; omega⟩,
      by omega⟩
