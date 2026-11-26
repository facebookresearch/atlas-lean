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
sums in the paper's proof.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuintuple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresTriple

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

/-- **Quintuple extensions come from a second semi-magic square.** Let $E = (e_{ij})$ be a
$3 \times 3$ integer matrix whose squared entries $e_{ij}^2$ have all three row sums and all three
column sums equal to one common integer. Put $(a_1, a_2, a_3) = (e_{13}^2, e_{31}^2, e_{22}^2)$ and
$(b_1, b_2, b_3) = (0, e_{21}^2 - e_{13}^2, e_{11}^2 - e_{22}^2)$, and let $a_4, a_5$ be integers
such that every sum $a_i + b_j$ with $1 \le i \le 5$ and $1 \le j \le 3$ is the square of an
integer. Then there is a $3 \times 3$ integer matrix $F = (f_{ij})$ whose squared entries also
have all row sums and all column sums equal to one common integer, with $f_{11}^2 = e_{11}^2$,
$f_{22}^2 = e_{22}^2$, $f_{33}^2 = e_{33}^2$, $a_4 = f_{13}^2$ and $a_5 = f_{31}^2$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted exists_isSemiMagicRoots_f_of_pairwiseSumsSquares_quintuple
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e)
    (a4 a5 : ℤ)
    (h : PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, a4, a5]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2]) :
    ∃ f : Fin 3 → Fin 3 → ℤ,
      IsSemiMagicRoots f ∧
        e 0 0 ^ 2 = f 0 0 ^ 2 ∧ e 1 1 ^ 2 = f 1 1 ^ 2 ∧
          e 2 2 ^ 2 = f 2 2 ^ 2 ∧
          a4 = f 0 2 ^ 2 ∧ a5 = f 2 0 ^ 2

/-- **Extending the triples to quadruples with square pairwise sums.** Let $E = (e_{ij})$,
$G = (g_{ij})$ and $H = (h_{ij})$ be $3 \times 3$ integer matrices, each of whose squared entries
have all three row sums and all three column sums equal to one common integer, such that
$e_{12}^2 = g_{12}^2$, $e_{13}^2 = g_{13}^2$, $e_{21}^2 = g_{21}^2$, $e_{31}^2 = g_{31}^2$,
$e_{11}^2 = h_{11}^2$, $e_{22}^2 = h_{22}^2$, $g_{11}^2 = h_{12}^2$ and $g_{22}^2 = h_{31}^2$. Put
$(a_1, a_2, a_3, a_4) = (e_{13}^2, e_{31}^2, e_{22}^2, g_{22}^2)$ and
$(b_1, b_2, b_3, b_4) = (0, e_{21}^2 - e_{13}^2, e_{11}^2 - e_{22}^2, g_{11}^2 - g_{22}^2)$. Then
$a_i + b_j$ is the square of an integer for all $1 \le i, j \le 4$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted pairwiseSumsSquares_quadruple_of_isSemiMagicRoots
    (e g h : Fin 3 → Fin 3 → ℤ)
    (he : IsSemiMagicRoots e) (hg : IsSemiMagicRoots g)
    (hh : IsSemiMagicRoots h)
    (h25 : e 0 1 ^ 2 = g 0 1 ^ 2 ∧ e 0 2 ^ 2 = g 0 2 ^ 2 ∧
      e 1 0 ^ 2 = g 1 0 ^ 2 ∧ e 2 0 ^ 2 = g 2 0 ^ 2)
    (h26 : e 0 0 ^ 2 = h 0 0 ^ 2 ∧ e 1 1 ^ 2 = h 1 1 ^ 2)
    (h27 : g 0 0 ^ 2 = h 0 1 ^ 2 ∧ g 1 1 ^ 2 = h 2 0 ^ 2) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, g 1 1 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2,
        g 0 0 ^ 2 - g 1 1 ^ 2]

/-- **Quadruple extensions come from two further semi-magic squares.** Let $E = (e_{ij})$ be a
$3 \times 3$ integer matrix whose squared entries $e_{ij}^2$ have all three row sums and all three
column sums equal to one common integer. Put $(a_1, a_2, a_3) = (e_{13}^2, e_{31}^2, e_{22}^2)$ and
$(b_1, b_2, b_3) = (0, e_{21}^2 - e_{13}^2, e_{11}^2 - e_{22}^2)$, and let $a_4, b_4$ be integers
such that every sum $a_i + b_j$ with $1 \le i, j \le 4$ is the square of an integer. Then there
are $3 \times 3$ integer matrices $G = (g_{ij})$ and $H = (h_{ij})$, each of whose squared entries
have all row sums and all column sums equal to one common integer, such that
$g_{12}^2 = e_{12}^2$, $g_{13}^2 = e_{13}^2$, $g_{21}^2 = e_{21}^2$, $g_{31}^2 = e_{31}^2$,
$h_{11}^2 = e_{11}^2$, $h_{22}^2 = e_{22}^2$, $h_{12}^2 = g_{11}^2$, $h_{31}^2 = g_{22}^2$,
$a_4 = g_{22}^2$ and $b_4 = g_{11}^2 - g_{22}^2$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e)
    (a4 b4 : ℤ)
    (h : PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, a4]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2, b4]) :
    ∃ g h : Fin 3 → Fin 3 → ℤ,
      IsSemiMagicRoots g ∧ IsSemiMagicRoots h ∧
        e 0 1 ^ 2 = g 0 1 ^ 2 ∧ e 0 2 ^ 2 = g 0 2 ^ 2 ∧
          e 1 0 ^ 2 = g 1 0 ^ 2 ∧ e 2 0 ^ 2 = g 2 0 ^ 2 ∧
          e 0 0 ^ 2 = h 0 0 ^ 2 ∧ e 1 1 ^ 2 = h 1 1 ^ 2 ∧
          g 0 0 ^ 2 = h 0 1 ^ 2 ∧ g 1 1 ^ 2 = h 2 0 ^ 2 ∧
          a4 = g 1 1 ^ 2 ∧ b4 = g 0 0 ^ 2 - g 1 1 ^ 2

/-- **Four-parameter triples with square pairwise sums, family (3.1).** For all integers
$p, q, r, s$, put $a_1 = 0$, $a_2 = 16pqrs$, $a_3 = (p+q+r+s)(p+q-r-s)(p-q+r-s)(p-q-r+s)$ and
$b_1 = 4(pr - qs)^2$, $b_2 = 4(ps - qr)^2$, $b_3 = 4(pq - rs)^2$. Then $a_i + b_j$ is a perfect
square for all $i, j \in \{1, 2, 3\}$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 1. -/
theorem_wanted pairwiseSumsSquares_triple_family31
    (p q r s : ℤ) :
    PairwiseSumsSquares
      ![0, 16 * p * q * r * s,
        (p + q + r + s) * (p + q - r - s) * (p - q + r - s) *
          (p - q - r + s)]
      ![4 * (p * r - q * s) ^ 2, 4 * (p * s - q * r) ^ 2,
        4 * (p * q - r * s) ^ 2]

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

/-- **Second three-parameter family of rational quadruples with square pairwise sums.** For
rational numbers $m, q, r$, let
$a_1 = 16 m^2 (m^4 - 1)^2 \bigl((m^6 - 2m^4 + 5m^2) q^2 + (2m^5 - 12m^3 + 2m) q r +
(5m^4 - 2m^2 + 1) r^2\bigr)^2$,
$a_2 = 16 m^2 (m^4 - 1)^2 \bigl((m^6 - 2m^4 + 5m^2) q^2 - (5m^4 - 2m^2 + 1) r^2\bigr)^2$,
$a_3 = (m^2 - 1)^2 \bigl((m^{10} + 26m^6 - 40m^4 - 3m^2) q^2 +
(2m^9 - 24m^7 + 76m^5 - 24m^3 + 2m) q r - (3m^8 + 40m^6 - 26m^4 - 1) r^2\bigr)^2$,
$a_4 = 16 m^2 (m^4 - 1)^2 \bigl((m^6 + 2m^4 - 7m^2) q^2 - (2m^5 - 12m^3 + 2m) q r -
(7m^4 - 2m^2 - 1) r^2\bigr)^2$,
$b_1 = 0$,
$b_2 = -4 m^2 \bigl((m^5 + 6m^3 - 3m) q - (5m^4 - 2m^2 + 1) r\bigr)
\bigl((3m^5 - 6m^3 - m) q + (5m^4 - 2m^2 + 1) r\bigr)
\bigl((m^5 - 2m^3 + 5m) q + (3m^4 - 6m^2 - 1) r\bigr)
\bigl((m^5 - 2m^3 + 5m) q - (m^4 + 6m^2 - 3) r\bigr)$,
$b_3 = -16 m^2 (m^2 + 1)^2 (m^2 - 1)^3 (q^2 - r^2)
\bigl((m^5 - 2m^4 + 6m^2 - m) q + (m^4 - 6m^3 + 2m - 1) r\bigr)
\bigl((m^5 + 2m^4 - 6m^2 - m) q + (m^4 + 6m^3 - 2m - 1) r\bigr)$ and
$b_4 = 128 m^3 (m^4 - 1)^3 (m r - q)(m^2 q^2 - r^2)\bigl((m^3 - 3m) q + (3m^2 - 1) r\bigr)$.
Then $a_i + b_j$ is the square of a rational number for all $1 \le i, j \le 4$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 4. -/
theorem_wanted pairwiseSumsSquares_quadruple_family59
    (m q r : ℚ) :
    PairwiseSumsSquares
      ![16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((m ^ 6 - 2 * m ^ 4 + 5 * m ^ 2) * q ^ 2 +
              (2 * m ^ 5 - 12 * m ^ 3 + 2 * m) * q * r +
              (5 * m ^ 4 - 2 * m ^ 2 + 1) * r ^ 2) ^ 2,
          16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((m ^ 6 - 2 * m ^ 4 + 5 * m ^ 2) * q ^ 2 -
              (5 * m ^ 4 - 2 * m ^ 2 + 1) * r ^ 2) ^ 2,
          (m ^ 2 - 1) ^ 2 *
            ((m ^ 10 + 26 * m ^ 6 - 40 * m ^ 4 - 3 * m ^ 2) * q ^ 2 +
              (2 * m ^ 9 - 24 * m ^ 7 + 76 * m ^ 5 - 24 * m ^ 3 +
                2 * m) * q * r -
              (3 * m ^ 8 + 40 * m ^ 6 - 26 * m ^ 4 - 1) * r ^ 2) ^ 2,
          16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((m ^ 6 + 2 * m ^ 4 - 7 * m ^ 2) * q ^ 2 -
              (2 * m ^ 5 - 12 * m ^ 3 + 2 * m) * q * r -
              (7 * m ^ 4 - 2 * m ^ 2 - 1) * r ^ 2) ^ 2]
      ![0,
        -4 * m ^ 2 * ((m ^ 5 + 6 * m ^ 3 - 3 * m) * q -
              (5 * m ^ 4 - 2 * m ^ 2 + 1) * r) *
          ((3 * m ^ 5 - 6 * m ^ 3 - m) * q +
            (5 * m ^ 4 - 2 * m ^ 2 + 1) * r) *
          ((m ^ 5 - 2 * m ^ 3 + 5 * m) * q +
            (3 * m ^ 4 - 6 * m ^ 2 - 1) * r) *
          ((m ^ 5 - 2 * m ^ 3 + 5 * m) * q -
            (m ^ 4 + 6 * m ^ 2 - 3) * r),
        -16 * m ^ 2 * (m ^ 2 + 1) ^ 2 * (m ^ 2 - 1) ^ 3 *
          (q ^ 2 - r ^ 2) *
          ((m ^ 5 - 2 * m ^ 4 + 6 * m ^ 2 - m) * q +
            (m ^ 4 - 6 * m ^ 3 + 2 * m - 1) * r) *
          ((m ^ 5 + 2 * m ^ 4 - 6 * m ^ 2 - m) * q +
            (m ^ 4 + 6 * m ^ 3 - 2 * m - 1) * r),
        128 * m ^ 3 * (m ^ 4 - 1) ^ 3 * (m * r - q) *
          (m ^ 2 * q ^ 2 - r ^ 2) *
          ((m ^ 3 - 3 * m) * q + (3 * m ^ 2 - 1) * r)]

end TwoSetsSumsetSquaresWanted

end NumberTheory

end MathlibExt
