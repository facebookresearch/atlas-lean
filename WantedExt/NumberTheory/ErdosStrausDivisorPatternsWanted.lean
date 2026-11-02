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

/-!
# Divisor criteria for Erdős–Straus solutions with prime denominator

Statement-only targets from Kyle Bradford, *Elementary Patterns from the Erdős-Straus
Conjecture*, INTEGERS 25 (2025), Article A54 (texts checked against arXiv:2403.16047v1,
Propositions 1, 3, 4). Equation (1) is `4/p = 1/x + 1/y + 1/z`. The bounds `⌈p/4⌉ ≤ x ≤ ⌈p/2⌉`
are written `(p + 3) / 4 ≤ x ≤ (p + 1) / 2` in `ℕ`. The paper's
`z = p(x + p x²/d)/(4x - p)` (type I) and `z = p(x + x²/d)/(4x - p)` (type II) are stated in the
equivalent division-free forms `(4x - p) d z = p x (p x + d)` and `(4x - p) d z = p x (x + d)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Type I Erdős–Straus triples from divisors of a square.** Let $p$ be a prime and let $x$ be a
natural number with $\lceil p/4 \rceil \le x \le \lceil p/2 \rceil$. If $d$ is a positive divisor
of $x^2$ with $d \equiv -px \pmod{4x - p}$, then there are natural numbers $y$ and $z$ with
$(4x - p)\,y = px + d$ and $(4x - p)\,d\,z = px(px + d)$ such that $x \le y \le z$ and $p \nmid y$.

Since $4x > p$, these equations say $y = (px + d)/(4x - p)$ and $z = p(x + px^2/d)/(4x - p)$.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 1 (`integers-2025-A54-prop-1`). -/
public theorem_wanted erdosStraus_typeI_of_dvd_sq {p x d : ℕ} (hp : p.Prime)
    (hx₁ : (p + 3) / 4 ≤ x) (hx₂ : x ≤ (p + 1) / 2) (hd₀ : 0 < d) (hd : d ∣ x ^ 2)
    (hmod : (4 * x - p : ℤ) ∣ d + p * x) :
    ∃ y z : ℕ, (4 * x - p : ℤ) * y = p * x + d ∧ (4 * x - p : ℤ) * d * z = p * x * (p * x + d) ∧
      x ≤ y ∧ y ≤ z ∧ ¬ p ∣ y

/-- **Divisor criterion necessary for type I Erdős–Straus solutions.** Let $p$ be a prime and let
$x \le y \le z$ be positive integers with $4/p = 1/x + 1/y + 1/z$ and $p \nmid y$. Then
$\lceil p/4 \rceil \le x \le \lceil p/2 \rceil$, and there is a positive divisor $d$ of $x^2$ with
$d \equiv -px \pmod{4x - p}$, $(4x - p)\,y = px + d$ and $(4x - p)\,d\,z = px(px + d)$.

Since $4x > p$, the last two equations say $y = (px + d)/(4x - p)$ and
$z = p(x + px^2/d)/(4x - p)$.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 3 (`integers-2025-A54-prop-3`). -/
public theorem_wanted erdosStraus_typeI_exists_dvd_sq {p x y z : ℕ} (hp : p.Prime) (hx : 0 < x)
    (hxy : x ≤ y) (hyz : y ≤ z) (h : (4 : ℚ) / p = 1 / x + 1 / y + 1 / z) (hpy : ¬ p ∣ y) :
    (p + 3) / 4 ≤ x ∧ x ≤ (p + 1) / 2 ∧
      ∃ d : ℕ, 0 < d ∧ d ∣ x ^ 2 ∧ (4 * x - p : ℤ) ∣ d + p * x ∧
        (4 * x - p : ℤ) * y = p * x + d ∧ (4 * x - p : ℤ) * d * z = p * x * (p * x + d)

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
