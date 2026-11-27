/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

/-!
# The abundancy surplus of an odd perfect number

The stronger inverse-square bound on the prime product gives the stated surplus bound
by comparing the logarithm of the least prime factor with the factor itself.

## References

* Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd Perfect or Odd
  Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59, pp. 1–21, Corollary 2
  (p. 13) and Proposition 5 (the stronger bound used here).
* D. Suryanarayana, *On odd perfect numbers III*, Proceedings of the American Mathematical
  Society 18 (1967), 933–939. Zelinsky credits this paper for the prime-product estimate in
  Lemma 9, used in the argument for Proposition 5.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

/-- **Surplus of an odd perfect number with least prime factor at least 11.** Let $n$ be an odd
perfect number whose least prime factor $p_1$ satisfies $p_1 \ge 11$, and let
$H(n) = \prod_{p \mid n} p/(p-1)$, the product over the primes $p$ dividing $n$. Then its surplus
$H(n) - 2$ satisfies $H(n) - 2 < \frac{25}{8 p_1 \log p_1}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Corollary 2 (`integers-2025-A59-cor-2`). -/
public theorem oddPerfect_abundancySup_sub_two_lt
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h11 : 11 ≤ n.minFac) :
    (abundancySup n : ℝ) - 2 < 25 / (8 * (n.minFac : ℝ) * Real.log n.minFac) := by
  have hone : (1 : ℝ) < n.minFac := by
    exact_mod_cast (show 1 < n.minFac from lt_of_lt_of_le (by decide : 1 < 11) h11)
  have hp : (0 : ℝ) < n.minFac := zero_lt_one.trans hone
  have hlog := Real.log_pos hone
  have hlog_lt : Real.log (n.minFac : ℝ) < n.minFac :=
    (Real.log_lt_sub_one_of_pos hp (ne_of_gt hone)).trans (sub_lt_self _ zero_lt_one)
  have hbound : (abundancySup n : ℝ) ≤ 2 + 9 / (4 * (n.minFac : ℝ) ^ 2) := by
    have h := Rat.cast_mono (K := ℝ) (oddPerfect_abundancySup_le n hodd hperf)
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_natCast] using h
  calc
    _ ≤ 9 / (4 * (n.minFac : ℝ) ^ 2) := by linarith only [hbound]
    _ < _ := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      have hmul := mul_lt_mul_of_pos_left hlog_lt hp
      nlinarith only [hmul, sq_pos_of_pos hp]

end MetaMathlibExt
