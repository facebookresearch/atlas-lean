/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.HyperbolicFloorSumAdditive
import Mathlib.Analysis.Asymptotics.Lemmas

open Asymptotics Filter Finset

namespace MetaMathlibExt.HyperbolicFloorSumAdditiveTest

-- With g constantly negative one, the additive function counts distinct primes with a minus sign.
private def negOmega (n : ℕ) : ℝ := -(n.primeFactors.card : ℝ)

private noncomputable def moment (i : ℕ) : ℝ :=
  ∑' n : ℕ, negOmega (n + 1) *
    (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))

-- For two factors the main polynomial is affine and the error scale is x log log x.
example (P : Polynomial ℝ)
    (hP : (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, ((Nat.finMulAntidiag 2 n).card : ℝ)) -
      x * P.eval (Real.log x)) =O[atTop] fun x : ℝ => x ^ (1 - 1 / (2 : ℝ))) :
    (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, negOmega ⌊x / n⌋₊ * (Nat.finMulAntidiag 2 n).card) -
      x * (P.coeff 0 * moment 0 + (P.coeff 1 * moment 0 * Real.log x - P.coeff 1 * moment 1)))
      =O[atTop] fun x : ℝ => x * Real.log (Real.log x) := by
  have hg : (fun _ : ℕ => (-1 : ℝ)) =O[atTop] fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2) := by
    apply IsBigO.of_bound'
    apply Eventually.of_forall
    intro n
    simpa [Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)] using
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by positivity : 0 ≤ (n : ℝ) / 2)
  have h := hyperbolic_floor_sum_asymptotic_additive 2 le_rfl P (by simpa using hP)
    (fun _ => -1) (by norm_num) hg
  simpa [sum_range_succ, negOmega, moment, sub_eq_add_neg] using h

end MetaMathlibExt.HyperbolicFloorSumAdditiveTest
