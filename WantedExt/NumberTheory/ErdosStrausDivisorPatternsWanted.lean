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

/-- Sufficient condition for a type I solution: if `p` is prime, `⌈p/4⌉ ≤ x ≤ ⌈p/2⌉`, and
`d > 0` divides `x²` with `d ≡ -p x (mod 4x - p)`, then `y = (p x + d)/(4x - p)` and
`z = p(x + p x²/d)/(4x - p)` are integers with `x ≤ y ≤ z` and `p ∤ y`.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 1 (`integers-2025-A54-prop-1`). -/
public theorem_wanted erdosStraus_typeI_of_dvd_sq {p x d : ℕ} (hp : p.Prime)
    (hx₁ : (p + 3) / 4 ≤ x) (hx₂ : x ≤ (p + 1) / 2) (hd₀ : 0 < d) (hd : d ∣ x ^ 2)
    (hmod : (4 * x - p : ℤ) ∣ d + p * x) :
    ∃ y z : ℕ, (4 * x - p : ℤ) * y = p * x + d ∧ (4 * x - p : ℤ) * d * z = p * x * (p * x + d) ∧
      x ≤ y ∧ y ≤ z ∧ ¬ p ∣ y

/-- Necessary condition for type I solutions: if `p` is prime and positive integers `x ≤ y ≤ z`
satisfy `4/p = 1/x + 1/y + 1/z` with `p ∤ y`, then `⌈p/4⌉ ≤ x ≤ ⌈p/2⌉` and some `d > 0` dividing
`x²` has `d ≡ -p x (mod 4x - p)`, `y = (p x + d)/(4x - p)` and `z = p(x + p x²/d)/(4x - p)`.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 3 (`integers-2025-A54-prop-3`). -/
public theorem_wanted erdosStraus_typeI_exists_dvd_sq {p x y z : ℕ} (hp : p.Prime) (hx : 0 < x)
    (hxy : x ≤ y) (hyz : y ≤ z) (h : (4 : ℚ) / p = 1 / x + 1 / y + 1 / z) (hpy : ¬ p ∣ y) :
    (p + 3) / 4 ≤ x ∧ x ≤ (p + 1) / 2 ∧
      ∃ d : ℕ, 0 < d ∧ d ∣ x ^ 2 ∧ (4 * x - p : ℤ) ∣ d + p * x ∧
        (4 * x - p : ℤ) * y = p * x + d ∧ (4 * x - p : ℤ) * d * z = p * x * (p * x + d)

/-- Necessary condition for type II solutions: if `p` is prime and positive integers `x ≤ y ≤ z`
satisfy `4/p = 1/x + 1/y + 1/z` with `p ∣ y`, then `⌈p/4⌉ ≤ x ≤ ⌈p/2⌉` and some `d > 0` dividing
`x²` has `d ≤ x`, `d ≡ -x (mod 4x - p)`, `y = p(x + d)/(4x - p)` and
`z = p(x + x²/d)/(4x - p)`.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 4 (`integers-2025-A54-prop-4`). -/
public theorem_wanted erdosStraus_typeII_exists_dvd_sq {p x y z : ℕ} (hp : p.Prime) (hx : 0 < x)
    (hxy : x ≤ y) (hyz : y ≤ z) (h : (4 : ℚ) / p = 1 / x + 1 / y + 1 / z) (hpy : p ∣ y) :
    (p + 3) / 4 ≤ x ∧ x ≤ (p + 1) / 2 ∧
      ∃ d : ℕ, 0 < d ∧ d ∣ x ^ 2 ∧ d ≤ x ∧ (4 * x - p : ℤ) ∣ d + x ∧
        (4 * x - p : ℤ) * y = p * (x + d) ∧ (4 * x - p : ℤ) * d * z = p * x * (x + d)

end

end MetaMathlibExt
