/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ErdosProblem729
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum

/-! # Tests for smooth denominators of factorial ratios -/

open MathlibExt.NumberTheory.ErdosProblem729Wanted

-- One cutoff continues to work after discarding any finite set of triples.
example (C : ℝ) (hC : 0 < C) :
    ∃ K ≥ 3, ∀ S : Finset (ℕ × ℕ × ℕ), ∃ a b n : ℕ, (a, b, n) ∉ S ∧
      0 < a ∧ 0 < b ∧ 0 < n ∧ (n : ℝ) + C * Real.log n < a + b ∧
      ∀ p, p.Prime → K < p → ¬ p ∣ ((n.factorial : ℚ) / (a.factorial * b.factorial)).den := by
  obtain ⟨K, hK, h⟩ := conjecture_holds C hC
  refine ⟨K, hK, fun S => ?_⟩
  obtain ⟨⟨a, b, n⟩, ⟨ha, hb, hn, hgap, hval⟩, hS⟩ := h.exists_notMem_finset S
  refine ⟨a, b, n, hS, ha, hb, hn, hgap, fun p hp hpK hd => ?_⟩
  have hv := hval p hp hpK
  rw [Nat.padicValNat_def, ← Nat.factorization_def _ hp] at hv
  exact (Nat.factorization_eq_zero_iff .. |>.mp hv).elim (· hp)
    (fun h => h.elim (· hd) (Rat.den_ne_zero _))

-- For (a, b, n) = (3, 7, 6), cancellation leaves the denominator 42.
-- The cutoff may include the prime 7 itself.
example :
    let d := ((Nat.factorial 6 : ℚ) / (Nat.factorial 3 * Nat.factorial 7)).den
    d = 42 ∧ padicValNat 7 d = 1 ∧ padicValNat 11 d = 0 := by
  norm_num [Nat.factorial]
  decide +kernel
