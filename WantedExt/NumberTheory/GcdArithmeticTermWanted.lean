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

/-- **The gcd terms in bases $2$, $3$ and $4$.** Let $c \in \{2, 3, 4\}$, let $a, b \ge 1$ be
natural numbers, and put $E = ab(ab + a + b)$ and $D = (c^{a^2 b} - 1)(c^{a b^2} - 1)$. Then the
identity
$$
\gcd(a, b) = \left( \lfloor c^E / D \rfloor \bmod c^{ab} \right) - 1
$$
holds if and only if $(a, b) \ne (1, 1)$, and the identity
$$
\gcd(a, b) = \big( ((-c^E) \bmod D) \bmod c^{ab} \big) - 2
$$
holds if and only if $(a, b) \ne (1, 1)$. Both identities are read in the integers, where
$x \bmod m$ is the remainder of $x$ in $\{0, \dots, m - 1\}$ for $m > 0$, also when $x < 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 2. -/
public theorem_wanted gcd_arithmetic_terms_small_bases (c : ℤ) (hc : c = 2 ∨ c = 3 ∨ c = 4)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((Nat.gcd a b : ℤ) =
        c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 1 ↔ (a, b) ≠ (1, 1)) ∧
      ((Nat.gcd a b : ℤ) =
        (-c ^ (a * b * (a * b + a + b))) % ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 2 ↔ (a, b) ≠ (1, 1))

end

end MetaMathlibExt
