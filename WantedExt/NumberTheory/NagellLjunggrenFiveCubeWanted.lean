/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MetaMathlibExt

@[expose] public section

/-- **Structure of a further solution of the Nagell–Ljunggren equation.** Let $x, y, n, q$ be
natural numbers with $x \ge 2$, $y \ge 2$, $n \ge 3$ and $q \ge 2$ such that
$(x^n - 1)/(x - 1) = y^q$, and suppose that $(x, y, n, q)$ is none of the known solutions
$(3, 11, 5, 2)$, $(7, 20, 4, 2)$ and $(18, 7, 3, 3)$. Then the least prime divisor of $n$ is at
least $29$, $n$ has at most four prime factors counted with multiplicity, $n$ is prime if
$q = 3$, and $n = q$ if $q \mid n$.

The source attributes the result to Bugeaud and Mihăilescu and to its references [2], [4].

Source: Tran Duc Son, *On the Nagell--Ljunggren Equation \frac{x^{5}-1}{x-1}=y^{3}*,
INTEGERS 26 (2026), Article A44, Theorem 2 (`integers-2026-A44-thm-2`). -/
public theorem_wanted nagell_ljunggren_exponent_structure (x y n q : ℕ) (hx : 2 ≤ x)
    (hy : 2 ≤ y) (hn : 3 ≤ n) (hq : 2 ≤ q) (h : (x ^ n - 1) / (x - 1) = y ^ q)
    (hnew : (x, y, n, q) ≠ (3, 11, 5, 2) ∧ (x, y, n, q) ≠ (7, 20, 4, 2) ∧
      (x, y, n, q) ≠ (18, 7, 3, 3)) :
    29 ≤ n.minFac ∧ ArithmeticFunction.cardFactors n ≤ 4 ∧ (q = 3 → n.Prime) ∧
      (q ∣ n → n = q)

/-- **The Nagell–Ljunggren cube equation when $5 \mid n$.** There are no natural numbers
$x \ge 2$, $y \ge 2$ and $n \ge 3$ with $5 \mid n$ such that $(x^n - 1)/(x - 1) = y^3$.

Source: Tran Duc Son, *On the Nagell--Ljunggren Equation \frac{x^{5}-1}{x-1}=y^{3}*,
INTEGERS 26 (2026), Article A44, Corollary 1 (`integers-2026-A44-cor-1`). -/
public theorem_wanted nagell_ljunggren_cube_of_five_dvd (x y n : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hn : 3 ≤ n) (h5 : 5 ∣ n) : (x ^ n - 1) / (x - 1) ≠ y ^ 3

end

end MetaMathlibExt
