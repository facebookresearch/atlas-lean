/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.ErdosStrausDivisorPatterns

/-!
# Divisor criteria for Erdős–Straus solutions with prime denominator

Statement-only target from Kyle Bradford, *Elementary Patterns from the Erdős-Straus
Conjecture*, INTEGERS 25 (2025), Article A54 (text checked against arXiv:2403.16047v1,
Proposition 4). Equation (1) is `4/p = 1/x + 1/y + 1/z`. The bounds `⌈p/4⌉ ≤ x ≤ ⌈p/2⌉`
are written `(p + 3) / 4 ≤ x ≤ (p + 1) / 2` in `ℕ`. The paper's type II
`z = p(x + x²/d)/(4x - p)` is stated in the equivalent division-free form
`(4x - p) d z = p x (x + d)`.

The type I divisor criteria, sufficient (`erdosStraus_typeI_of_dvd_sq`) and necessary
(`erdosStraus_typeI_exists_dvd_sq`), are proved in
`MathlibExt.NumberTheory.ErdosStrausDivisorPatterns`, which this module imports.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Divisor criterion necessary for type II Erdős–Straus solutions.** Let $p$ be a prime and let
$x \le y \le z$ be positive integers with $4/p = 1/x + 1/y + 1/z$ and $p \mid y$. Then
$\lceil p/4 \rceil \le x \le \lceil p/2 \rceil$, and there is a positive divisor $d$ of $x^2$ with
$d \le x$, $d \equiv -x \pmod{4x - p}$, $(4x - p)\,y = p(x + d)$ and $(4x - p)\,d\,z = px(x + d)$.

Since $4x > p$, the last two equations say $y = p(x + d)/(4x - p)$ and
$z = p(x + x^2/d)/(4x - p)$.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 4 (`integers-2025-A54-prop-4`). -/
public theorem_wanted erdosStraus_typeII_exists_dvd_sq {p x y z : ℕ} (hp : p.Prime) (hx : 0 < x)
    (hxy : x ≤ y) (hyz : y ≤ z) (h : (4 : ℚ) / p = 1 / x + 1 / y + 1 / z) (hpy : p ∣ y) :
    (p + 3) / 4 ≤ x ∧ x ≤ (p + 1) / 2 ∧
      ∃ d : ℕ, 0 < d ∧ d ∣ x ^ 2 ∧ d ≤ x ∧ (4 * x - p : ℤ) ∣ d + x ∧
        (4 * x - p : ℤ) * y = p * (x + d) ∧ (4 * x - p : ℤ) * d * z = p * x * (x + d)

end

end MetaMathlibExt
