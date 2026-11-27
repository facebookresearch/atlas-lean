/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two sets whose sumset elements are squares

Statements from Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
*INTEGERS* 26 (2026), Article A66
(<https://math.colgate.edu/~integers/aa66/aa66.pdf>).

Finite families are indexed by `Fin m` and `Fin n`; the paper's
one-based index `1` is Lean index `0` here.  A `3 × 3` matrix with
squared entries is represented by its integer roots
`e : Fin 3 → Fin 3 → ℤ`, with matrix entries `(e i j)^2`.
Semi-magic means all row sums and all column sums of those squared
entries have one common value.

Lemma 2 is split into the actual construction and converse
statements used in its proof, rather than the bare existence
formulation.  This avoids a vacuous reading in which both sides are
satisfied independently by zero examples: the forward parts start
from given semi-magic root matrices, and the converse parts produce
the matrices `E₁`, `F₁`, `G₁`, and `H₁` built from the pairwise
sums in the paper's proof.  The forward part for quintuples,
`exists_isSemiMagicRoots_f_of_pairwiseSumsSquares_quintuple`, is
proved in
`MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsFOfPairwiseSumsSquaresQuintuple`.
The statement
`exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple` is
proved in
`MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsGhOfPairwiseSumsSquaresQuadruple`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuadruple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuintuple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresTriple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresTripleFamily31
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsFOfPairwiseSumsSquaresQuintuple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsGhOfPairwiseSumsSquaresQuadruple

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- **Triples with square pairwise sums from a semi-magic square of squares.** Let $e_{ij}$,
$1 \le i, j \le 3$, be integers such that the matrix of squares $(e_{ij}^2)$ is semi-magic, that
is, all its row sums and all its column sums are equal. Put $a_1 = e_{13}^2$, $a_2 = e_{31}^2$,
$a_3 = e_{22}^2$ and $b_1 = 0$, $b_2 = e_{21}^2 - e_{13}^2$, $b_3 = e_{11}^2 - e_{22}^2$. Then
$a_i + b_j$ is a perfect square for all $i, j \in \{1, 2, 3\}$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted pairwiseSumsSquares_triple_of_isSemiMagicRoots
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2]

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
theorem_wanted pairwiseSumsSquares_quintuple_family41
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
          (f ^ 2 * u2 ^ 2 - g ^ 2 * v2 ^ 2)]

end TwoSetsSumsetSquaresWanted

end NumberTheory

end MathlibExt
