/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# The Nagell–Ljunggren equation `(xⁿ - 1)/(x - 1) = y^q` (statements)

Statement-only targets from Tran Duc Son, *A Note on the Nagell–Ljunggren Equation
`(xⁿ - 1)/(x - 1) = y³`*. Theorem 2 and Corollary 1 concern `q = 3` with `x ≡ 2, 3, 5, 6 (mod 9)`;
Theorem 1, quoted from Ljunggren, concerns the general exponent `q ≥ 2`. The equation is written
without division as `xⁿ - 1 = (x - 1) y^q`, which is equivalent because `x ≠ 1`: in Theorem 2 and
Corollary 1 since `x ≢ 1 (mod 9)`, in Theorem 1 since `1 < x.natAbs`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 2: for `n ≡ 5 (mod 6)`, the equation `(xⁿ - 1)/(x - 1) = y³` has no integer
solutions `(x, y)` with `x ≡ 2, 3, 5, 6 (mod 9)` (the paper's `x = 9z + 2, 9z + 3, 9z + 5,
9z + 6` with `z ∈ ℤ`).

Source: Tran Duc Son, *A Note on the Nagell–Ljunggren Equation (xⁿ - 1)/(x - 1) = y³*,
INTEGERS 26 (2026), Article A104, Theorem 2 (`integers-2026-A104-thm-2`). -/
public theorem_wanted nagell_ljunggren_cube_no_solution_of_mod_six_eq_five (n : ℕ)
    (hn : n % 6 = 5) (x y : ℤ) (hx : x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 5 ∨ x % 9 = 6) :
    x ^ n - 1 ≠ (x - 1) * y ^ 3

/-- Corollary 1: the equation `(xⁿ - 1)/(x - 1) = y³` has no integer solutions `(x, y, n)`
with `x ≡ 2, 3, 5, 6 (mod 9)`. The record's Equation (1) is not displayed; `n` ranges over
`n ≥ 3`, the classical range `n > 2` of the Nagell–Ljunggren equation (for `n = 1` every `x`
gives the solution `y = 1`).

Source: Tran Duc Son, *A Note on the Nagell–Ljunggren Equation (xⁿ - 1)/(x - 1) = y³*,
INTEGERS 26 (2026), Article A104, Corollary 1 (`integers-2026-A104-cor-1`). -/
public theorem_wanted nagell_ljunggren_cube_no_solution (n : ℕ) (hn : 3 ≤ n) (x y : ℤ)
    (hx : x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 5 ∨ x % 9 = 6) :
    x ^ n - 1 ≠ (x - 1) * y ^ 3

/-- Theorem 1 (Ljunggren, quoted from the literature): consider `(xⁿ - 1)/(x - 1) = y^q` in
integers `|x| > 1` (as `1 < x.natAbs`), `y > 1`, `n > 2`, `q ≥ 2` (Equation (1)). Apart from
`(3⁵ - 1)/(3 - 1) = 11²`, `(7⁴ - 1)/(7 - 1) = 20²`, `(18³ - 1)/(18 - 1) = 7³` and
`((-19)³ - 1)/(-19 - 1) = 7³`, it has no solution `(x, y, n, q)` if `q = 2`, or `3 ∣ n`, or
`4 ∣ n`, or `q = 3` and `n ≢ 5 (mod 6)`. The equation is written as `xⁿ - 1 = (x - 1) y^q`
(equivalent since `x ≠ 1`).

Source: Tran Duc Son, *A Note on the Nagell–Ljunggren Equation (xⁿ - 1)/(x - 1) = y³*,
INTEGERS 26 (2026), Article A104, Theorem 1, quoting Ljunggren (`integers-2026-A104-thm-1`). -/
public theorem_wanted nagell_ljunggren_solutions_of_conditions (x y : ℤ) (n q : ℕ)
    (hx : 1 < x.natAbs) (hy : 1 < y) (hn : 2 < n) (hq : 2 ≤ q)
    (heq : x ^ n - 1 = (x - 1) * y ^ q)
    (hcond : q = 2 ∨ 3 ∣ n ∨ 4 ∣ n ∨ (q = 3 ∧ n % 6 ≠ 5)) :
    (x, y, n, q) = (3, 11, 5, 2) ∨ (x, y, n, q) = (7, 20, 4, 2) ∨ (x, y, n, q) = (18, 7, 3, 3) ∨
      (x, y, n, q) = (-19, 7, 3, 3)

end

end MetaMathlibExt
