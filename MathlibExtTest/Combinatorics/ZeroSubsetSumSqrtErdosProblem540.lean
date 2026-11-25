/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540
import Mathlib.Tactic.Linarith

open MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540Wanted

example : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ A : Finset (ZMod N),
    C * Real.sqrt N ≤ A.card → ∃ S ⊆ A, S.Nonempty ∧ ∑ x ∈ S, x = 0 :=
  sqrtSizeHasZeroSubsetSum_holds

-- A sufficiently large square modulus allows an input set that excludes zero.
example : ∃ (m : ℕ) (S : Finset (ZMod (m ^ 2))),
    1 < m ∧ 0 ∉ S ∧ S.Nonempty ∧ ∑ x ∈ S, x = 0 := by
  obtain ⟨C, _, hC⟩ := sqrtSizeHasZeroSubsetSum_holds
  obtain ⟨k, hk⟩ := exists_nat_gt (max C 1)
  let m := k + 1
  have hk1 : 1 < (k : ℝ) := (le_max_right _ _).trans_lt hk
  have hm : 1 < m := by
    have hkpos : 0 < k := by exact_mod_cast (show 0 < (k : ℝ) by linarith)
    omega
  have hm2 : 0 < m ^ 2 := pow_pos (by omega) _
  let : NeZero (m ^ 2) := ⟨Nat.ne_of_gt hm2⟩
  let A : Finset (ZMod (m ^ 2)) := Finset.univ.erase 0
  have hA : C * Real.sqrt ((m ^ 2 : ℕ) : ℝ) ≤ A.card := by
    have hcard : A.card + 1 = m ^ 2 := by
      simp [A, ZMod.card, Nat.sub_add_cancel hm2]
    have hcard' : (A.card : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hcard
    have hCk : C ≤ (k : ℝ) := ((le_max_left _ _).trans_lt hk).le
    have hm' : (k : ℝ) + 1 = (m : ℝ) := by simp [m]
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
    nlinarith only [hcard', hm', hk1, mul_le_mul_of_nonneg_right hCk (Nat.cast_nonneg m)]
  obtain ⟨S, hS, hne, hsum⟩ := hC (m ^ 2) hm2 A hA
  exact ⟨m, S, hm, fun hz => by simpa [A] using hS hz, hne, hsum⟩
