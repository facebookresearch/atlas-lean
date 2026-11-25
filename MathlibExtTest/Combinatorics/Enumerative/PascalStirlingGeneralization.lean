/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PascalStirlingGeneralization
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt.PascalStirlingGeneralizationTest

-- The `3 × 3` factorial matrix of a power series `f`: the entry in row `a` and column `b ≤ a` is
-- `a! / b!` times the coefficient of `t^(a-b)`, so the last row carries `2!/0! = 2!/1! = 2`.
example (f : PowerSeries ℚ) :
    powerSeriesFactorialMatrix f 3 =
      !![PowerSeries.coeff 0 f, 0, 0;
        PowerSeries.coeff 1 f, PowerSeries.coeff 0 f, 0;
        2 * PowerSeries.coeff 2 f, 2 * PowerSeries.coeff 1 f, PowerSeries.coeff 0 f] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [powerSeriesFactorialMatrix, Nat.factorial]

/-- The factorial matrix of the power series `1` is the identity matrix. -/
private theorem powerSeriesFactorialMatrix_one (n : ℕ) :
    powerSeriesFactorialMatrix (1 : PowerSeries ℚ) n = 1 := by
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · rw [powerSeriesFactorialMatrix_apply_self, Matrix.one_apply_eq, PowerSeries.coeff_zero_one]
  · have hab' : (a : ℕ) ≠ b := Fin.val_ne_iff.mpr hab
    rw [Matrix.one_apply_ne hab]
    simp only [powerSeriesFactorialMatrix, Matrix.of_apply, PowerSeries.coeff_one]
    split_ifs with h1 h2
    · omega
    · rw [mul_zero]
    · rfl

/-- The factorial matrix of `exp` is the Pascal matrix: its entry in row `a` and column `b` is the
binomial coefficient `a.choose b`. -/
private theorem powerSeriesFactorialMatrix_exp_apply (n : ℕ) (a b : Fin n) :
    powerSeriesFactorialMatrix (PowerSeries.exp ℚ) n a b = ((a : ℕ).choose b : ℚ) := by
  simp only [powerSeriesFactorialMatrix, Matrix.of_apply, PowerSeries.coeff_exp,
    Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs with h
  · rw [Nat.cast_choose ℚ h]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

-- Multiplicativity inverts the Pascal matrix: `M_n(exp) M_n(exp(-t)) = M_n(1) = 1`.
example (n : ℕ) :
    powerSeriesFactorialMatrix (PowerSeries.exp ℚ) n *
      powerSeriesFactorialMatrix (PowerSeries.evalNegHom (PowerSeries.exp ℚ)) n = 1 := by
  rw [powerSeriesFactorialMatrix_mul, PowerSeries.exp_mul_exp_neg_eq_one,
    powerSeriesFactorialMatrix_one]

-- Multiplicativity squares the Pascal matrix: since `exp(t)^2 = exp(2t)`,
-- `∑_c C(a, c) C(c, b) = 2^(a-b) C(a, b)` for `b ≤ a < n`.
example (n : ℕ) (a b : Fin n) (hba : b ≤ a) :
    ∑ c : Fin n, ((a : ℕ).choose c : ℚ) * ((c : ℕ).choose b : ℚ) =
      2 ^ ((a : ℕ) - b) * ((a : ℕ).choose b : ℚ) := by
  have h := congrFun₂ (powerSeriesFactorialMatrix_mul (PowerSeries.exp ℚ) (PowerSeries.exp ℚ) n) a b
  simp only [Matrix.mul_apply, powerSeriesFactorialMatrix_exp_apply] at h
  rw [h, ← pow_two, PowerSeries.exp_pow_eq_rescale_exp]
  simp only [powerSeriesFactorialMatrix, Matrix.of_apply, ite_eq_left (show (b : ℕ) ≤ a from hba),
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp, Algebra.algebraMap_self, RingHom.id_apply,
    Nat.cast_choose ℚ (show (b : ℕ) ≤ a from hba)]
  push_cast
  field_simp

-- Factorial matrices of power series commute with each other.
example (f g : PowerSeries ℚ) (n : ℕ) :
    powerSeriesFactorialMatrix f n * powerSeriesFactorialMatrix g n =
      powerSeriesFactorialMatrix g n * powerSeriesFactorialMatrix f n := by
  rw [powerSeriesFactorialMatrix_mul, powerSeriesFactorialMatrix_mul, mul_comm]

end MetaMathlibExt.PascalStirlingGeneralizationTest
