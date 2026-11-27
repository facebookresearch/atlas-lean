/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.NagellLjunggrenCubeNoSolution
public import MathlibExt.NumberTheory.NagellLjunggrenCubeResidues

/-!
# The Nagell–Ljunggren equation `(xⁿ - 1)/(x - 1) = y^q` (statements)

Ljunggren’s classification under conditions on the exponents, as quoted in Tran Duc Son,
*A Note on the Nagell–Ljunggren Equation `(xⁿ - 1)/(x - 1) = y³`*. The hypothesis
`1 < x.natAbs` permits the equation to be written without division.
-/

namespace MetaMathlibExt

@[expose] public section

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
