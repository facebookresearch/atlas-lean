/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted

-- At zero the first derivative counts the three transpositions with negative sign.
example :
    (∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      Fintype.card (Function.fixedPoints σ) * 0 ^ (Fintype.card (Function.fixedPoints σ) - 1)) =
      -3 := by
  have h := sum_perm_sign_falling_fixedPoints_mul_pow 3 1 (by decide) (by decide) (by decide) 0
  norm_num [Nat.factorial, Finset.prod_range_succ] at h
  exact h

-- At one the extreme derivative order k = n - 1 gives n!, including the zero exponent.
example :
    (∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ((Fintype.card (Function.fixedPoints σ) : ℝ) *
        (Fintype.card (Function.fixedPoints σ) - (1 : ℝ)))) = 6 := by
  have h := sum_perm_sign_falling_fixedPoints_mul_pow 3 2 (by decide) (by decide) (by decide) 1
  norm_num [Nat.factorial, Finset.prod_range_succ] at h
  exact h

-- For three points the identity, the three transpositions and the two 3-cycles give
-- 3!/5! - 3 * 1!/3! + 2 * 0!/2! = 11/20.
example :
    (∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ((Nat.factorial (Fintype.card (Function.fixedPoints σ)) : ℝ) /
        (Nat.factorial (Fintype.card (Function.fixedPoints σ) + 2) : ℝ))) = 11 / 20 := by
  rw [sum_perm_sign_factorial_fixedPoints_div 3 2 (by decide) (by decide)]
  norm_num [Nat.factorial]

-- At order one, where `(k - 1)! = 0!`, the identity reads
-- ∑ sgn σ / (fix σ + 1) = (-1)^(n+1) n / (n + 1).
example (n : ℕ) (hn : 2 ≤ n) :
    (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) /
      ((Fintype.card (Function.fixedPoints σ) : ℝ) + 1)) =
      (-1 : ℝ) ^ (n + 1) * n / (n + 1) := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ((Nat.factorial (Fintype.card (Function.fixedPoints σ)) : ℝ) /
            (Nat.factorial (Fintype.card (Function.fixedPoints σ) + 1) : ℝ)) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      have : (Nat.factorial (Fintype.card (Function.fixedPoints σ)) : ℝ) ≠ 0 := by positivity
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    _ = _ := by
      rw [sum_perm_sign_factorial_fixedPoints_div n 1 hn le_rfl]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      norm_num
      field_simp
