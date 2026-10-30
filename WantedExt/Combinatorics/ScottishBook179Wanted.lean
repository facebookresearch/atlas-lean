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
The sharp Littlewood-Offord bound answering Offord's Problem 179 from
the Scottish Book: for real `a 0, ..., a n` with `1 ≤ |a i|`, the number
of sign choices `ε` for which the signed sum `a 0 + ∑ ε i * a (i + 1)`
falls in `(-1, 1)` is at most `A * 2 ^ n / √n` for an absolute constant
`A`. In the original notation the bound is on the exceptional set of
signed sums `a 0 + ε 1 a 1 + ... + ε n a n` whose absolute value is
below `min |a nu|`; the statement here is the rescaled form with
`min |a nu| = 1`. Source: A. C. Offord, Problem 179 of the Scottish
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
