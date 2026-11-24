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

/-- **The Nagell–Ljunggren cube equation for $n \equiv 5 \pmod 6$.** Let $n$ be a natural
number with $n \equiv 5 \pmod 6$. Then there are no integers $x$ and $y$ with
$x \equiv 2, 3, 5$ or $6 \pmod 9$ such that $x^n - 1 = (x - 1) y^3$. Since such an $x$ is not
$1$, this says that $(x^n - 1)/(x - 1) = y^3$ has no such integer solution.

Source: Tran Duc Son, *A Note on the Nagell–Ljunggren Equation (xⁿ - 1)/(x - 1) = y³*,
INTEGERS 26 (2026), Article A104, Theorem 2 (`integers-2026-A104-thm-2`). -/
public theorem_wanted nagell_ljunggren_cube_no_solution_of_mod_six_eq_five (n : ℕ)
    (hn : n % 6 = 5) (x y : ℤ) (hx : x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 5 ∨ x % 9 = 6) :
    x ^ n - 1 ≠ (x - 1) * y ^ 3

/-- **The Nagell–Ljunggren cube equation for $x \equiv 2, 3, 5, 6 \pmod 9$.** Let $n \ge 3$ be a
natural number. Then there are no integers $x$ and $y$ with $x \equiv 2, 3, 5$ or $6 \pmod 9$
such that $x^n - 1 = (x - 1) y^3$. Since such an $x$ is not $1$, this says that
$(x^n - 1)/(x - 1) = y^3$ has no such integer solution.

The bound $n \ge 3$ is the classical range $n > 2$ of the Nagell–Ljunggren equation; for $n = 1$
every $x$ gives the solution $y = 1$.

Source: Tran Duc Son, *A Note on the Nagell–Ljunggren Equation (xⁿ - 1)/(x - 1) = y³*,
INTEGERS 26 (2026), Article A104, Corollary 1 (`integers-2026-A104-cor-1`). -/
public theorem_wanted nagell_ljunggren_cube_no_solution (n : ℕ) (hn : 3 ≤ n) (x y : ℤ)
    (hx : x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 5 ∨ x % 9 = 6) :
    x ^ n - 1 ≠ (x - 1) * y ^ 3

/-- **Ljunggren's theorem on the Nagell–Ljunggren equation.** Let $x$ and $y$ be integers and
$n$ and $q$ natural numbers with $|x| > 1$, $y > 1$, $n > 2$ and $q \ge 2$, and suppose that
$x^n - 1 = (x - 1) y^q$, that is, $(x^n - 1)/(x - 1) = y^q$ (as $x \ne 1$). If $q = 2$, or
$3 \mid n$, or $4 \mid n$, or $q = 3$ and $n \not\equiv 5 \pmod 6$, then $(x, y, n, q)$ is one
of $(3, 11, 5, 2)$, $(7, 20, 4, 2)$, $(18, 7, 3, 3)$ and $(-19, 7, 3, 3)$.

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
