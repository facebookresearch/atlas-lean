/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NondecreasingDyckSubwords

/-!
# Tests for subwords in non-decreasing Dyck paths

The tests cover overlapping triples, valley-free paths, and peak and valley totals by semilength.
-/

open MetaMathlibExt DyckStep

example : PowerSeries.coeff 0 (nondecreasingDyckSubwordBivariateGF [U, U, U]) = 0 := by
  simp [nondecreasingDyckSubwordBivariateGF]

example : nondecreasingDyckSubwordTotal [U, U, U] 0 = 0 := by decide +kernel

example : dyckSubwordCount [U, U, U] [U, U, U, U, D, D, D, D] = 2 := by decide

example : nondecreasingDyckSubwordTotal [U, U, U] 4 = 6 := by decide +kernel

example : nondecreasingDyckSubwordTotal [D, U] 1 = 0 := by decide +kernel

-- The alternating path contributes two valleys at semilength three.
example : ((nondecreasingDyckWords 3).filter fun p =>
    dyckSubwordCount [D, U] p.val.toList = 2).card = 1 := by decide +kernel

-- Semilength four is the first at which the non-decreasing restriction removes a path.
example : nondecreasingDyckSubwordTotal [D, U] 4 = 19 := by decide +kernel

example : PowerSeries.coeff 0 (nondecreasingDyckSubwordBivariateGF [U, D]) = 0 := by
  simp [nondecreasingDyckSubwordBivariateGF]

example : nondecreasingDyckSubwordTotal [U, D] 0 = 0 := by decide +kernel

example : nondecreasingDyckSubwordTotal [U, D] 1 = 1 := by decide +kernel

-- Check the last initial value and the first value governed by the homogeneous recurrence.
example : nondecreasingDyckSubwordTotal [U, D] 4 = 32 := by decide +kernel

example : nondecreasingDyckSubwordTotal [U, D] 5 = 99 := by decide +kernel

-- Only UDUDUD contributes two overlapping copies of UDU at semilength three.
example : ((nondecreasingDyckWords 3).filter fun p =>
    dyckSubwordCount [U, D, U] p.val.toList = 2).card = 1 := by decide +kernel

-- Semilength five is the first term determined by the homogeneous recurrence.
example : nondecreasingDyckSubwordTotal [U, D, U] 5 = 46 := by decide +kernel

-- No path of this semilength can contain a run of four up steps.
example : nondecreasingDyckSubwordTotal (List.replicate 4 U) 3 = 0 := by
  decide +kernel

-- Only the pyramid contributes at the threshold.
example : nondecreasingDyckSubwordTotal (List.replicate 4 U) 4 = 1 := by
  decide +kernel

-- At m = 1 and n = 2, the Fibonacci sum is empty and the n - 2 term is at zero.
example : nondecreasingDyckSubwordTotal (List.replicate 1 U) 2 = 4 := by
  have h := (nondecreasingDyck_subword_U_pow 1 (by decide)).1 2 (by decide)
  have h₀ : nondecreasingDyckSubwordTotal (List.replicate 1 U) 0 = 0 := by decide +kernel
  have h₁ : nondecreasingDyckSubwordTotal (List.replicate 1 U) 1 = 1 := by decide +kernel
  rw [show (2 : ℕ) - 1 = 1 by decide, show (2 : ℕ) - 2 = 0 by decide, h₀, h₁] at h
  norm_num [Finset.Icc_eq_empty (by decide : ¬ (1 : ℕ) ≤ 1 - 2)] at h
  exact_mod_cast h

-- Both terms in the correction sum can contribute at this interior point.
example : nondecreasingDyckSubwordTotal (List.replicate 4 U) 6 = 30 := by
  have h := (nondecreasingDyck_subword_U_pow 4 (by decide)).1 6 (by decide)
  have h₄ : nondecreasingDyckSubwordTotal (List.replicate 4 U) 4 = 1 := by decide +kernel
  have h₅ : nondecreasingDyckSubwordTotal (List.replicate 4 U) 5 = 7 := by decide +kernel
  have hi : Finset.Icc 1 (4 - 2 : ℕ) = {1, 2} := by decide
  rw [show (6 : ℕ) - 1 = 5 by decide, show (6 : ℕ) - 2 = 4 by decide, h₄, h₅, hi] at h
  norm_num [Finset.sum_insert, Nat.fib] at h
  exact_mod_cast h
