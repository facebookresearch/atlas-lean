/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SL2TwoStepProductGrowth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.SL2TwoStepProductGrowth` -/

namespace MathlibExtTest.SL2TwoStepProductGrowth

open MathlibExt.Combinatorics.SL2TwoStepProductGrowthWanted

-- Test section: the product set `A · A`, which contains products of distinct elements.
example : AIMCombinatorics0241_prodSet ({1, 2} : Finset ℕ) = {1, 2, 4} := by decide

-- The product set of a singleton `{g}` is `{g * g}`.
example {G : Type*} [Monoid G] [DecidableEq G] (g : G) :
    AIMCombinatorics0241_prodSet ({g} : Finset G) = {g * g} := by
  simp [AIMCombinatorics0241_prodSet]

-- The product set of the empty set is empty.
example {G : Type*} [Mul G] [DecidableEq G] :
    AIMCombinatorics0241_prodSet (∅ : Finset G) = ∅ := by
  simp [AIMCombinatorics0241_prodSet]

-- Test section: the theorem. With `C = 2`, the hypotheses may be given separately.
example : ∃ δ : ℝ, 0 < δ ∧ ∃ P0 : ℕ, ∀ p : ℕ, P0 ≤ p → Nat.Prime p →
    ∀ A : Finset (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
      (1 / 2) * Real.rpow (p : ℝ) (5 / 2 : ℝ) ≤ (A.card : ℝ) →
      (A.card : ℝ) ≤ 2 * Real.rpow (p : ℝ) (5 / 2 : ℝ) →
      Real.rpow (p : ℝ) (5 / 2 + δ) < ((AIMCombinatorics0241_prodSet A).card : ℝ) := by
  obtain ⟨δ, hδ, P0, h⟩ := conjecture_holds 2 (by norm_num)
  exact ⟨δ, hδ, P0, fun p hp hpr A h1 h2 => h p hp hpr A ⟨h1, h2⟩⟩

-- For large primes, a set of size about `p ^ (5 / 2)` has a product set of size more than
-- `p ^ (5 / 2)`: the exponent `5 / 2 + δ` of the theorem is at least `5 / 2` since `p ≥ 1`.
example (C : ℝ) (hC : 1 ≤ C) : ∃ P0 : ℕ, ∀ p : ℕ, P0 ≤ p → Nat.Prime p →
    ∀ A : Finset (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
      (1 / C) * (p : ℝ) ^ (5 / 2 : ℝ) ≤ A.card → (A.card : ℝ) ≤ C * (p : ℝ) ^ (5 / 2 : ℝ) →
      (p : ℝ) ^ (5 / 2 : ℝ) < (AIMCombinatorics0241_prodSet A).card := by
  obtain ⟨δ, hδ, P0, h⟩ := conjecture_holds C hC
  refine ⟨P0, fun p hp hpr A h1 h2 => ?_⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpr.one_lt.le
  calc (p : ℝ) ^ (5 / 2 : ℝ) ≤ (p : ℝ) ^ (5 / 2 + δ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ < _ := h p hp hpr A ⟨h1, h2⟩

end MathlibExtTest.SL2TwoStepProductGrowth
