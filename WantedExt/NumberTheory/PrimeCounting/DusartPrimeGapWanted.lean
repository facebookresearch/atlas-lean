/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Dusart's short-interval prime gap bound.** Let $\log$ be the natural logarithm. For every
real number $x \ge 468991632$ there is a prime $p$ with $x < p \le x + \frac{x}{5000 (\log x)^2}$.

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Corollary 5.5. -/
theorem_wanted dusart_prime_gap (x : ℝ) (hx : 468991632 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ)
      ∧ (p : ℝ) ≤ x + x / (5000 * (Real.log x) ^ 2)

end

end MetaMathlibExt
