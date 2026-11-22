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

/-- Structure of a hypothetical further solution of the Nagell–Ljunggren equation
`(xⁿ - 1)/(x - 1) = y^q` (Equation (1)): if `(x, y, n, q)` is a solution other than the three
known ones `(3, 11, 5, 2)`, `(7, 20, 4, 2)`, `(18, 7, 3, 3)` (Equation (2)), then the least
prime divisor of `n` is at least `29` and `Ω(n) ≤ 4`; moreover `n` is prime if `q = 3`, and
`q ∣ n` implies `n = q`. `Ω(n)` (prime divisors counted with multiplicity) is
`ArithmeticFunction.cardFactors n`. The ranges `x, y ≥ 2`, `n ≥ 3`, `q ≥ 2` are the standard
ones of Equation (1), the same as in `MetaMathlibExt.nagell_ljunggren_solutions` (the
quoted Theorem 1 of the source, with the same exceptional solutions); the equation's display
is not in the extracted text. The source attributes the result to Bugeaud and Mihăilescu and
to its references [2], [4].

Source: Tran Duc Son, *On the Nagell--Ljunggren Equation \frac{x^{5}-1}{x-1}=y^{3}*,
INTEGERS 26 (2026), Article A44, Theorem 2 (`integers-2026-A44-thm-2`). -/
public theorem_wanted nagell_ljunggren_exponent_structure (x y n q : ℕ) (hx : 2 ≤ x)
    (hy : 2 ≤ y) (hn : 3 ≤ n) (hq : 2 ≤ q) (h : (x ^ n - 1) / (x - 1) = y ^ q)
    (hnew : (x, y, n, q) ≠ (3, 11, 5, 2) ∧ (x, y, n, q) ≠ (7, 20, 4, 2) ∧
      (x, y, n, q) ≠ (18, 7, 3, 3)) :
    29 ≤ n.minFac ∧ ArithmeticFunction.cardFactors n ≤ 4 ∧ (q = 3 → n.Prime) ∧
      (q ∣ n → n = q)

/-- The Nagell–Ljunggren equation `(xⁿ - 1)/(x - 1) = y³` (Equation (1) with `q = 3`) has no
solution with `5 ∣ n`. Ranges as in `nagell_ljunggren_exponent_structure`: `x, y ≥ 2`,
`n ≥ 3`.

Source: Tran Duc Son, *On the Nagell--Ljunggren Equation \frac{x^{5}-1}{x-1}=y^{3}*,
INTEGERS 26 (2026), Article A44, Corollary 1 (`integers-2026-A44-cor-1`). -/
public theorem_wanted nagell_ljunggren_cube_of_five_dvd (x y n : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hn : 3 ≤ n) (h5 : 5 ∣ n) : (x ^ n - 1) / (x - 1) ≠ y ^ 3

end

end MetaMathlibExt
