/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanHarmonicIdentity
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

-- At the first recurrence index, the normalization gives twice K(2) equal to three times K(1).
example
    (K : ℕ → ℂ)
    (hK : ∀ n : ℕ, 2 ≤ n →
      ∑ ν ∈ Finset.Icc 2 n,
          (((Nat.choose (2 * n - ν - 2) (n - 1) : ℂ) -
            (Nat.choose (2 * n - ν - 2) (n - 2) : ℂ)) * K ν) =
        (Nat.choose (2 * n - 1) (n - 1) : ℂ) * (K (n - 1) - K n)) :
    2 * K 2 = 3 * K 1 := by
  obtain ⟨c, hc⟩ := eq_lambda_mul_harmonic_of_sum_choose_sub_mul_eq K hK
  rw [hc 2 (by decide), hc 1 (by decide)]
  norm_num [harmonic, Finset.sum_range_succ]
  ring

-- A sequence supported at zero satisfies the hypothesis for any value at zero.
example (z : ℂ) :
    ∃ c : ℂ, ∀ r : ℕ, 1 ≤ r → (if r = 0 then z else 0) = c * (harmonic r : ℂ) := by
  apply eq_lambda_mul_harmonic_of_sum_choose_sub_mul_eq (fun r => if r = 0 then z else 0)
  intro n hn
  rw [Finset.sum_eq_zero]
  · simp [show n - 1 ≠ 0 by omega, show n ≠ 0 by omega]
  · intro ν hν
    have := (Finset.mem_Icc.mp hν).1
    simp [show ν ≠ 0 by omega]
