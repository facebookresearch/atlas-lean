/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoSetsSumsetSquares

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.Basic

/-!
# A seven-parameter quintuple and triple with square pairwise sums

For arbitrary rational `f`, `g`, `m`, `u1`, `u2`, `v1`, and `v2`, the quintuple and triple in
Equation (4.1) of Choudhry's Theorem 2 have all fifteen pairwise sums equal to rational squares.
The proof reads the roots from the two specialized Euler matrices and checks the polynomial
identities directly.

## References

* Ajai Choudhry, [*Two Sets of Integers Such That All Elements of the Sumset of the Two Sets
  Are Perfect Squares*](https://math.colgate.edu/~integers/aa66/aa66.pdf), *INTEGERS* 26 (2026),
  Article A66, pp. 1–17, Theorem 2, Equations (4.1)–(4.3), (4.7), and (4.9), and Lemma 2,
  Equations (2.2)–(2.4).
* L. E. Dickson, *History of the Theory of Numbers*, Vol. II, Chelsea, New York, 1992, p. 530,
  for Euler's semi-magic matrix as cited by Choudhry for Equation (2.10).
* The Lean proof follows the root table and finite case split of
  `pairwiseSumsSquares_triple_family31` in
  `MathlibExt.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresTripleFamily31`.
-/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- **A seven-parameter family of five and three rationals with square pairwise sums.** For
rational numbers $f, g, m, u_1, u_2, v_1, v_2$, put
$\alpha = m u_1 u_2 (u_1 v_1 - u_2 v_2)$, $\beta = (u_1 v_2 - u_2 v_1)(m^2 u_1 u_2 v_1 v_2 - 1)$,
$\gamma = m v_1 v_2 (u_1 v_1 - u_2 v_2)$, $\alpha' = m u_1 u_2 (u_1 v_1 + u_2 v_2)$,
$\beta' = (u_1 v_2 + u_2 v_1)(m^2 u_1 u_2 v_1 v_2 + 1)$ and
$\gamma' = m v_1 v_2 (u_1 v_1 + u_2 v_2)$, and let
$a_1 = 4(\alpha f^2 - \beta f g - \gamma g^2)^2$,
$a_2 = 4(\alpha' f^2 + \beta' f g + \gamma' g^2)^2$,
$a_3 = \bigl((u_1^2 u_2^2 (v_1^2 - v_2^2) m^2 + u_1^2 - u_2^2) f^2 -
(v_1^2 v_2^2 (u_1^2 - u_2^2) m^2 + v_1^2 - v_2^2) g^2\bigr)^2$,
$a_4 = 4(\alpha f^2 + \beta f g - \gamma g^2)^2$,
$a_5 = 4(\alpha' f^2 - \beta' f g + \gamma' g^2)^2$,
$b_1 = 0$,
$b_2 = -4 (u_1^2 - u_2^2)(v_1^2 - v_2^2)(m^2 u_1^2 u_2^2 f^2 - g^2)(f^2 - m^2 v_1^2 v_2^2 g^2)$
and
$b_3 = 4 (m^2 u_1^2 v_1^2 - 1)(m^2 u_2^2 v_2^2 - 1)(f^2 u_1^2 - g^2 v_1^2)(f^2 u_2^2 - g^2 v_2^2)$.
Then $a_i + b_j$ is the square of a rational number for all $1 \le i \le 5$ and $1 \le j \le 3$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 2. -/
public theorem pairwiseSumsSquares_quintuple_family41
    (f g m u1 u2 v1 v2 : ℚ) :
    PairwiseSumsSquares
      ![4 * (m * u1 * u2 * (u1 * v1 - u2 * v2) * f ^ 2 -
            (u1 * v2 - u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 - 1) *
              f * g -
            m * v1 * v2 * (u1 * v1 - u2 * v2) * g ^ 2) ^ 2,
        4 * (m * u1 * u2 * (u1 * v1 + u2 * v2) * f ^ 2 +
            (u1 * v2 + u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 + 1) *
              f * g +
            m * v1 * v2 * (u1 * v1 + u2 * v2) * g ^ 2) ^ 2,
        ((u1 ^ 2 * u2 ^ 2 * (v1 ^ 2 - v2 ^ 2) * m ^ 2 +
              u1 ^ 2 - u2 ^ 2) * f ^ 2 -
            (v1 ^ 2 * v2 ^ 2 * (u1 ^ 2 - u2 ^ 2) * m ^ 2 +
              v1 ^ 2 - v2 ^ 2) * g ^ 2) ^ 2,
        4 * (m * u1 * u2 * (u1 * v1 - u2 * v2) * f ^ 2 +
            (u1 * v2 - u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 - 1) *
              f * g -
            m * v1 * v2 * (u1 * v1 - u2 * v2) * g ^ 2) ^ 2,
        4 * (m * u1 * u2 * (u1 * v1 + u2 * v2) * f ^ 2 -
            (u1 * v2 + u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 + 1) *
              f * g +
            m * v1 * v2 * (u1 * v1 + u2 * v2) * g ^ 2) ^ 2]
      ![0,
        -4 * (u1 ^ 2 - u2 ^ 2) * (v1 ^ 2 - v2 ^ 2) *
          (m ^ 2 * u1 ^ 2 * u2 ^ 2 * f ^ 2 - g ^ 2) *
          (f ^ 2 - m ^ 2 * v1 ^ 2 * v2 ^ 2 * g ^ 2),
        4 * (m ^ 2 * u1 ^ 2 * v1 ^ 2 - 1) *
          (m ^ 2 * u2 ^ 2 * v2 ^ 2 - 1) *
          (f ^ 2 * u1 ^ 2 - g ^ 2 * v1 ^ 2) *
          (f ^ 2 * u2 ^ 2 - g ^ 2 * v2 ^ 2)] := by
  -- Rearrange the roots in the Euler matrix to match the sum indices in Lemma 2.
  let rows (p q r s : ℚ) : Fin 3 → Fin 3 → ℚ :=
    ![![2 * (q * s - p * r), 2 * (q * r - p * s), 2 * (r * s - p * q)],
      ![2 * (q * s + p * r), 2 * (q * r + p * s), 2 * (p * q + r * s)],
      ![p ^ 2 - q ^ 2 + r ^ 2 - s ^ 2, p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2,
        p ^ 2 + q ^ 2 - r ^ 2 - s ^ 2]]
  let e := g * m * v1 * v2
  let h := f * m * u1 * u2
  let roots₁ := rows (e * u1 + f * u2) (e * u2 + f * u1) (g * v1 + h * v2) (g * v2 + h * v1)
  let roots₂ := rows (e * u1 - f * u2) (e * u2 - f * u1) (g * v1 - h * v2) (g * v2 - h * v1)
  let roots : Fin 5 → Fin 3 → ℚ := ![roots₁ 0, roots₁ 1, roots₁ 2, roots₂ 0, roots₂ 1]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, roots₁, roots₂, rows, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [e, h, Matrix.cons_val] <;> ring1

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
