/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.Combinatorics.ScottishBook179Wanted

/--
**Sharp Littlewood–Offord bound.** There is a real constant $A \ge 0$ such that for every
integer $n \ge 1$ and all real numbers $a_0, a_1, \dots, a_n$ with $|a_i| \ge 1$ for every $i$,
the number of sign vectors $(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ with
$|a_0 + \varepsilon_1 a_1 + \dots + \varepsilon_n a_n| < 1$ is at most $A \cdot 2^n / \sqrt{n}$.

This answers Offord's Problem 179 from the Scottish Book. In the original notation the bound is
on the exceptional set of signed sums $a_0 + \varepsilon_1 a_1 + \dots + \varepsilon_n a_n$
whose absolute value is below $\min_\nu |a_\nu|$; the statement here is the rescaled form with
$\min_\nu |a_\nu| = 1$.

Source: A. C. Offord, Problem 179 of the Scottish
Book; the Littlewood-Offord lemma (Littlewood-Offord, 1938) and Erdős's
proof giving the sharp `O(2 ^ n / √n)` bound, attained when all the
`a nu` are equal. See the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted littlewoodOffordSharpBound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (a : Fin (n + 1) → ℝ),
      (∀ i, 1 ≤ |a i|) →
      ((Finset.univ.filter (fun ε : Fin n → Bool =>
        |a 0 + ∑ i : Fin n, (if ε i then (1 : ℝ) else -1) * a (Fin.succ i)| < 1)).card :
        ℝ) ≤ A * (2 : ℝ) ^ n / Real.sqrt n

end MathlibExt.Combinatorics.ScottishBook179Wanted
