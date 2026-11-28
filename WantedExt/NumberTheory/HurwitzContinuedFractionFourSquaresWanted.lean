/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.HurwitzContinuedFractionFourSquares

/-!
# Sums of four squares via Hurwitz complex continued fractions

Statements from Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex
Continued Fractions*, INTEGERS 24 (2024), Article A25 (arXiv:2205.00642; TeX source read for
the definitions).

The Hurwitz algorithm expands `z = z_0 ∈ ℂ` by `a_n = [z_n]` (the nearest Gaussian integer,
`hurwitzRound`) and `z_{n+1} = (z_n - a_n)⁻¹` (`hurwitzIter`); the `Q`-pairs are
`P_{-1} = 1, P_0 = a_0, P_{n+1} = a_{n+1} P_n + P_{n-1}` and
`Q_{-1} = 0, Q_0 = 1, Q_{n+1} = a_{n+1} Q_n + Q_{n-1}` (`hurwitzP`, `hurwitzQ`). The paper's
nearest-integer rounding does not fix ties; we round halves up (`⌊t + 1/2⌋`). An index `n` is
*legal* (`HurwitzLegal z n`) when the expansion has not terminated before step `n`, i.e.
`z_j ≠ a_j` for all `j < n`; for `z ∈ ℚ[i]` with expansion `[a_0; …, a_m]` these are the
`n ≤ m`. After termination Lean's `0⁻¹ = 0` gives `z_{m+1} = 0`.
-/

open Complex

namespace MetaMathlibExt

@[expose] public section

/-- **Lakein's first theorem on Hurwitz convergents.** Let $z$ be a complex number and let $P_k$
and $Q_k$ be the convergent numerators and denominators of its Hurwitz continued fraction
expansion. For every legal index $k$ for $z$ (the expansion has not terminated before step $k$),
$|z - P_k / Q_k| \le 1 / |Q_k|^2$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Lemma 2 (`integers-2024-A25-lem-2`). -/
public theorem_wanted norm_sub_hurwitz_convergent_le (z : ℂ) (k : ℕ) (hk : HurwitzLegal z k) :
    ‖z - hurwitzP z k / hurwitzQ z k‖ ≤ 1 / ‖hurwitzQ z k‖ ^ 2

/-- **Sums of four squares via Hurwitz continued fractions.** Let $w$, $x$, $y$ be natural numbers
such that $w$ is odd and not a perfect square, $2x < w$, $2y < w$ and $w$ divides
$x^2 + y^2 + 1$. Expand $z = (x + yi)/w$ by the Hurwitz algorithm, with convergent numerators
$P_n$ and convergent denominators $Q_n$. Then there is exactly one natural number $n$ such that
$n + 1$ is a legal index for $z$, $|Q_n| \le \sqrt{w} < |Q_{n+1}|$, and, if $|Q_n| \ne \sqrt{w}$,
$w = |(x + yi) Q_n - w P_n|^2 + |Q_n|^2$.

When it holds, the last identity is a representation of $w$ as a sum of four squares.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Theorem 1 (`integers-2024-A25-thm-1`). -/
public theorem_wanted hurwitz_four_squares (w x y : ℕ) (hw : Odd w) (hsq : ¬ IsSquare w)
    (hx : 2 * x < w) (hy : 2 * y < w) (hmod : w ∣ x ^ 2 + y ^ 2 + 1) :
    let z : ℂ := (x + y * I) / w
    ∃! n, HurwitzLegal z (n + 1) ∧ ‖hurwitzQ z n‖ ≤ Real.sqrt w ∧
        Real.sqrt w < ‖hurwitzQ z (n + 1)‖ ∧
        (‖hurwitzQ z n‖ ≠ Real.sqrt w →
          (w : ℝ) = normSq ((x + y * I) * hurwitzQ z n - w * hurwitzP z n) +
            normSq (hurwitzQ z n))

end

end MetaMathlibExt
