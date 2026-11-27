/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The logarithm of a central binomial coefficient

`log_centralBinom` writes $\log\binom{2n}{n}$ through factorials. It is shared by the asymptotics of
products of central binomial coefficients and by the estimates for primes of the form $6k - 1$.
-/

namespace MetaMathlibExt

/-- **The logarithm of a central binomial coefficient.** For every natural number $n$,
$$\log\binom{2n}{n} = \log\,(2n)! - 2\log n!.$$ -/
public theorem log_centralBinom (n : ℕ) :
    Real.log n.centralBinom = Real.log (2 * n).factorial - 2 * Real.log n.factorial := by
  have h : (n.centralBinom : ℝ) * n.factorial * n.factorial = (2 * n).factorial := by
    exact_mod_cast (by simpa [Nat.centralBinom_eq_two_mul_choose, two_mul] using
      Nat.add_choose_mul_factorial_mul_factorial n n :
        n.centralBinom * n.factorial * n.factorial = (2 * n).factorial)
  have hb : (0 : ℝ) < n.centralBinom := by exact_mod_cast n.centralBinom_pos
  rw [← h, Real.log_mul (by positivity) (by positivity),
    Real.log_mul hb.ne' (by positivity)]
  ring

end MetaMathlibExt
