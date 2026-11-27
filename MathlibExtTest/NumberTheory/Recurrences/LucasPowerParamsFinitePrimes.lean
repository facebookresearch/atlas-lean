/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.LucasPowerParamsFinitePrimes

open MetaMathlibExt

-- The root of larger absolute value is negative. Its square yields a prime term at index two.
example : {n : ℕ | (lucasU ⟨5, 4, by decide⟩ n).natAbs.Prime}.Finite ∧
    (lucasU ⟨5, 4, by decide⟩ 2).natAbs.Prime := by
  refine ⟨lucasU_power_params_finite_primes (x := 1) (y := -2) (a := -1) (b := -2) (r := 2)
    (hxy := by norm_num) (hs := by norm_num) (hp := by norm_num) (hr := by decide)
    (hQ := by decide) (hPdef := by norm_num) (hQdef := by norm_num)
    (hP := by decide) (hD := by decide), by decide⟩

-- Cubing the Fibonacci roots gives Q = -1, and the term at index three is prime.
example : {n : ℕ | (lucasU ⟨4, -1, by decide⟩ n).natAbs.Prime}.Finite ∧
    (lucasU ⟨4, -1, by decide⟩ 3).natAbs.Prime := by
  let t := Real.sqrt 5
  have ht : t ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have htpos : 0 < t := Real.sqrt_pos.mpr (by norm_num)
  have hprod : (1 + t) / 2 * ((1 - t) / 2) = (-1 : ℝ) := by nlinarith only [ht]
  refine ⟨lucasU_power_params_finite_primes
    (x := (1 + t) / 2) (y := (1 - t) / 2) (a := 1) (b := -1) (r := 3)
    (hxy := by linarith) (hs := by norm_num; ring) (hp := by exact_mod_cast hprod)
    (hr := by decide) (hQ := by decide) (hPdef := by nlinarith only [ht])
    (hQdef := by rw [← mul_pow, hprod]; norm_num) (hP := by decide) (hD := by decide),
    by decide⟩
