/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.GcdArithmeticTerm

namespace MetaMathlibExt

@[expose] public section

/-- **Arithmetic term for the gcd in base $5$.** For all natural numbers $a, b \ge 1$,
$$
\gcd(a, b) + 1 = \left\lfloor \frac{5^{ab(ab+a+b)}}{(5^{a^2 b} - 1)(5^{a b^2} - 1)} \right\rfloor
\bmod 5^{ab},
$$
that is, $\gcd(a, b)$ is one less than the remainder of this floor modulo $5^{ab}$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Theorem 1. -/
public theorem_wanted gcd_add_one_eq_floor_div_mod_five (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.gcd a b + 1 =
      5 ^ (a * b * (a * b + a + b)) / ((5 ^ (a ^ 2 * b) - 1) * (5 ^ (a * b ^ 2) - 1)) %
        5 ^ (a * b)

end

end MetaMathlibExt
