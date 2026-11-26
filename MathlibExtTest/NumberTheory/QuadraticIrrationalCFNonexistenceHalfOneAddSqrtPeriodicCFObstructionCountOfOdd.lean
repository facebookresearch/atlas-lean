/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistenceHalfOneAddSqrtPeriodicCFObstructionCountOfOdd
import Mathlib.Data.ZMod.Defs
import MathlibExt.NumberTheory.SymmetricContinuantParity
import MathlibExt.NumberTheory.SymmetricConvergentDenParity

/-! # Tests for realized parity patterns at odd period length -/

namespace MathlibExtTest.NumberTheory.QuadraticIrrationalCFNonexistenceHalfOneAddSqrtPeriodicCFObstructionCountOfOdd

open MetaMathlibExt

-- At length five, the pattern `j ↦ if j = 0 then 1 else 0` is realized.
example : ∃ a : ℕ → ℕ, ((a 1 : ℕ) : ZMod 2) = 1 ∧ ((a 2 : ℕ) : ZMod 2) = 0 ∧
    (∀ i, 1 ≤ i → i < 5 → 0 < a i) ∧
    (∀ i, 1 ≤ i → i < 5 → a i = a (5 - i)) ∧
    ∃ d a₀ : ℕ, ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a 5 (2 * a₀ - 1) := by
  have h := half_one_add_sqrt_periodicCF_obstruction_count_of_odd 5 ⟨2, rfl⟩
  rw [Set.ncard_eq_zero ((Set.finite_univ).subset (Set.subset_univ _)),
    Set.eq_empty_iff_forall_notMem] at h
  have hv := h (fun j : Fin (5 / 2) => if (j : ℕ) = 0 then 1 else 0)
  simp only [Set.mem_ofPred_eq, not_not] at hv
  obtain ⟨a, hpos, hsymm, hmatch, d, a₀, hnsq, hcf⟩ := hv
  have h1 : ((a 1 : ℕ) : ZMod 2) = 1 := hmatch ⟨0, by decide⟩
  have h2 : ((a 2 : ℕ) : ZMod 2) = 0 := hmatch ⟨1, by decide⟩
  exact ⟨a, h1, h2, hpos, hsymm, d, a₀, hnsq, hcf⟩

-- At length three, the constant pattern `1` is realized.
example : ∃ a : ℕ → ℕ, ((a 1 : ℕ) : ZMod 2) = 1 ∧
    (∀ i, 1 ≤ i → i < 3 → 0 < a i) ∧
    (∀ i, 1 ≤ i → i < 3 → a i = a (3 - i)) ∧
    ∃ d a₀ : ℕ, ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a 3 (2 * a₀ - 1) := by
  have h := half_one_add_sqrt_periodicCF_obstruction_count_of_odd 3 ⟨1, rfl⟩
  rw [Set.ncard_eq_zero ((Set.finite_univ).subset (Set.subset_univ _)),
    Set.eq_empty_iff_forall_notMem] at h
  have hv := h (fun _ : Fin (3 / 2) => (1 : ZMod 2))
  simp only [Set.mem_ofPred_eq, not_not] at hv
  obtain ⟨a, hpos, hsymm, hmatch, d, a₀, hnsq, hcf⟩ := hv
  have h1 : ((a 1 : ℕ) : ZMod 2) = 1 := hmatch ⟨0, by decide⟩
  exact ⟨a, h1, hpos, hsymm, d, a₀, hnsq, hcf⟩

-- At length one, the unique pattern is realized.
example : ∃ a : ℕ → ℕ, ∃ d a₀ : ℕ, ¬IsSquare d ∧
    HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a 1 (2 * a₀ - 1) := by
  have h := half_one_add_sqrt_periodicCF_obstruction_count_of_odd 1 ⟨0, rfl⟩
  rw [Set.ncard_eq_zero ((Set.finite_univ).subset (Set.subset_univ _)),
    Set.eq_empty_iff_forall_notMem] at h
  have hv := h Fin.elim0
  simp only [Set.mem_ofPred_eq, not_not] at hv
  obtain ⟨a, -, -, -, d, a₀, hnsq, hcf⟩ := hv
  exact ⟨a, d, a₀, hnsq, hcf⟩

end MathlibExtTest.NumberTheory.QuadraticIrrationalCFNonexistenceHalfOneAddSqrtPeriodicCFObstructionCountOfOdd
