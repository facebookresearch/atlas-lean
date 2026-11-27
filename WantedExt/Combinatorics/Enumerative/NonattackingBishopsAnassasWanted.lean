/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.NonattackingBishopsAnassas
public import MathlibExt.Combinatorics.Enumerative.BishopsArshonReindex

/-!
# Counting nonattacking placements of bishops and anassas

Statements from Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and
Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6 (preprint arXiv:2411.16492,
from which the definitions are taken).

* A board is a finite set of squares `(i, j) ∈ ℤ²`; a piece with basic moves `M` attacks along
  the lines through its square in the directions of `M`, so a placement is nonattacking when no
  two of its squares differ by a rational multiple of a move (`nonattackingPlacements`).
* `squareBoard m = [1, m]²`. The paper's white and black boards `W_m`, `K_m` are the
  diagonals of the white and black squares of `S_m` drawn as rows and columns, so rooks on
  `W_m` (resp. `K_m`) are bishops on the squares of `S_m` with `i + j` even (resp. odd); the
  counts `R_W`, `R_K` are taken in that form (`whiteSquares`, `blackSquares`; the single square
  of `S_1` is white).
* The bishop has moves `(1, 1), (-1, 1)`; the anassa `(0, 1), (1, 1)`, and "strictly below the
  main diagonal" means `j < i`.
* The paper uses the extended Stirling numbers of the second kind of Knuth, defined for all
  integer arguments by `{n, k} = [-k, -n]` (unsigned first kind) for negative arguments and `0`
  for mixed signs (`extStirlingSecond`); its associated Stirling numbers of the second kind
  `{{n, k}}` are the canonical `twoAssocStirlingSecond` (integer-valued), and `Ring.choose` is the
  binomial coefficient with arbitrary
  top argument.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-! ## Collapsible boards -/

/-! Theorem 1.2 (`jis-2025-25.8.6-thm-2`) is not stated: see the audit table. -/

/-! ## The bishop -/

/-- **Recurrence for bishops on white squares.** Write $R_W(m, k)$ for the number of placements of
$k$ nonattacking bishops on the white squares (those $(i, j)$ with $i + j$ even) of the
$m \times m$ board $[1, m]^2$, and $\pi(n) \in \lbrace 0, 1 \rbrace$ for the remainder of $n$
modulo $2$. For all natural numbers $m$ and $k$,

$$
R_W(m + 1, k + 1) = R_W(m, k + 1) + \bigl(m - k + \pi(m + 1)\bigr) R_W(m, k),
$$

$R_W(m, 0) = 1$ and $R_W(0, k + 1) = 0$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsWhite_recurrence (m k : ℕ) :
    (bishopsWhite (m + 1) (k + 1) : ℤ) =
        bishopsWhite m (k + 1) + ((m : ℤ) - k + ((m + 1) % 2 : ℕ)) * bishopsWhite m k ∧
      bishopsWhite m 0 = 1 ∧ bishopsWhite 0 (k + 1) = 0

/-- **Extended Stirling formula for bishops on white squares.** For all natural numbers $m$ and
$k$, the number $R_W(m, k)$ of placements of $k$ nonattacking bishops on the white squares (those
$(i, j)$ with $i + j$ even) of the $m \times m$ board $[1, m]^2$ satisfies

$$
R_W(m, k) = \sum_{j=0}^{k} \binom{\lceil m/2 \rceil}{j} S(m - j, m - k),
$$

where $S(a, b)$ is Knuth's extended Stirling number of the second kind for integers $a, b$: the
Stirling number of the second kind when $a, b \ge 0$, the unsigned Stirling number of the first
kind with arguments $-b, -a$ when $a, b < 0$, and $0$ otherwise.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsWhite_eq_sum (m k : ℕ) :
    bishopsWhite m k =
      ∑ j ∈ range (k + 1), ((m + 1) / 2).choose j * extStirlingSecond ((m : ℤ) - j) ((m : ℤ) - k)

/-- **Sum formula for bishops on the black squares.** Let $R_K(m, k)$ be the number of
nonattacking placements of $k$ bishops on the black squares $(i, j)$, with $i + j$ odd, of the
board $\{1, \dots, m\}^2$, and let ${n \brace j}$ be Knuth's extended Stirling numbers of the
second kind. For all natural numbers $m$ and $k$,
$$R_K(m, k) = \sum_{j=0}^{k} \binom{\lfloor m/2 \rfloor}{j} {m-j \brace m-k}.$$

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsBlack_eq_sum (m k : ℕ) :
    bishopsBlack m k =
      ∑ j ∈ range (k + 1), (m / 2).choose j * extStirlingSecond ((m : ℤ) - j) ((m : ℤ) - k)

/-- **Santos's expansion of a product of binomial coefficients.** For natural numbers $p$, $q$
and complex numbers $x$, $z$,
$$\binom{2x + z - q}{p} \binom{x}{q} = \sum_{i=0}^{p+q} \beta_i(p, q, z) \binom{2x + z}{i},$$
where $\beta_i(p, q, z)$ are Santos's coefficients and, for complex $w$ and natural $n$,
$\binom{w}{n} = w(w-1)\cdots(w-n+1)/n!$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 9 (`jis-2025-25.8.6-lem-9`). -/
public theorem_wanted choose_mul_choose_eq_sum_santosBeta (p q : ℕ) (x z : ℂ) :
    Ring.choose (2 * x + z - q) p * Ring.choose x q =
      ∑ i ∈ range (p + q + 1), santosBeta i p q z * Ring.choose (2 * x + z) i

/-- **Quasi-polynomial formula for bishops on white squares.** Write $R_W(m, k)$ for the number of
placements of $k$ nonattacking bishops on the white squares (those $(i, j)$ with $i + j$ even) of
the $m \times m$ board $[1, m]^2$, $\pi(m) \in \lbrace 0, 1 \rbrace$ for the remainder of $m$
modulo $2$, and $c_{k,d}(z) \in \mathbb{C}$ for the constituent coefficient of the bishop colour
quasi-polynomials (defined for natural $k, d$ and complex $z$). For all natural numbers $m$ and
$k$, as complex numbers,

$$
R_W(m, k) = \sum_{d=0}^{2k} c_{k,d}\bigl(-\pi(m)\bigr)\, m^d.
$$

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 10 (`jis-2025-25.8.6-thm-10`). -/
public theorem_wanted bishopsWhite_eq_quasi (m k : ℕ) :
    (bishopsWhite m k : ℂ) =
      ∑ d ∈ range (2 * k + 1), bishopColorQuasiCoeff k d (-((m % 2 : ℕ) : ℂ)) * (m : ℂ) ^ d

/-- **Quasi-polynomial formula for bishops on the black squares.** Let $R_K(m, k)$ be the
number of nonattacking placements of $k$ bishops on the black squares $(i, j)$, with $i + j$
odd, of the board $\{1, \dots, m\}^2$, and let $c_{k,d}(z)$ be the constituent coefficients of
the bishop quasi-polynomials. For all natural numbers $m$ and $k$,
$$R_K(m, k) = \sum_{d=0}^{2k} c_{k,d}(\pi(m)) \, m^d$$
in $\mathbb{C}$, where $\pi(m) \in \{0, 1\}$ is the remainder of $m$ modulo $2$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 10 (`jis-2025-25.8.6-thm-10`). -/
public theorem_wanted bishopsBlack_eq_quasi (m k : ℕ) :
    (bishopsBlack m k : ℂ) =
      ∑ d ∈ range (2 * k + 1), bishopColorQuasiCoeff k d ((m % 2 : ℕ) : ℂ) * (m : ℂ) ^ d

/-- **Quasi-polynomial formula for bishops on a square board.** Write $B_S(m, k)$ for the number of
placements of $k$ nonattacking bishops on the $m \times m$ board $[1, m]^2$,
$\pi(m) \in \lbrace 0, 1 \rbrace$ for the remainder of $m$ modulo $2$, and
$c_{k,d}(z) \in \mathbb{C}$ for the constituent coefficient of the bishop colour quasi-polynomials
(defined for natural $k, d$ and complex $z$). For all natural numbers $m$ and $k$, as complex
numbers,

$$
B_S(m, k) = \sum_{d=0}^{2k} \Biggl( \sum_{j=0}^{k} \sum_{i=0}^{d}
c_{j,i}\bigl(-\pi(m)\bigr)\, c_{k-j,\,d-i}\bigl(\pi(m)\bigr) \Biggr) m^d.
$$

The factors $c_{j,i}(-\pi(m))$ and $c_{k-j,d-i}(\pi(m))$ are the coefficients of the corresponding
quasi-polynomial formulas for bishops on the white and on the black squares.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 10 (`jis-2025-25.8.6-thm-10`). -/
public theorem_wanted bishopsSquare_eq_quasi (m k : ℕ) :
    (bishopsSquare m k : ℂ) =
      ∑ d ∈ range (2 * k + 1),
        (∑ j ∈ range (k + 1), ∑ i ∈ range (d + 1),
          bishopColorQuasiCoeff j i (-((m % 2 : ℕ) : ℂ)) *
            bishopColorQuasiCoeff (k - j) (d - i) ((m % 2 : ℕ) : ℂ)) * (m : ℂ) ^ d

/-! ## The anassa -/

/-- **Sum formula for anassas below the diagonal.** Let $A(m, k, p)$ be the number of
nonattacking placements of $k$ anassas on the square board $\{1, \dots, m\}^2$ with exactly $p$
of them strictly below the main diagonal, and let ${n \brace j}$ be Knuth's extended Stirling
numbers of the second kind. For natural numbers $m$, $k$, $p$ with $p \le k$,
$$A(m, k, p) = \sum_{j=0}^{p} (m-k+j)_j \binom{k-p-1}{j} \binom{k-j}{k-p}
{m+1 \brace m-k+j+1}$$
in the integers, where $(x)_j = x(x-1)\cdots(x-j+1)$ is the falling factorial and
$\binom{k-p-1}{j}$ is the generalized binomial coefficient, so that $\binom{-1}{j} = (-1)^j$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 11 (`jis-2025-25.8.6-thm-11`). -/
public theorem_wanted anassasBelow_eq_sum (m k p : ℕ) (hp : p ≤ k) :
    (anassasBelow m k p : ℤ) =
      ∑ j ∈ range (p + 1),
        (∏ t ∈ range j, ((m : ℤ) - k + j - t)) * Ring.choose ((k : ℤ) - p - 1) j *
          ((k - j).choose (k - p) : ℤ) * extStirlingSecond (m + 1 : ℕ) ((m : ℤ) - k + j + 1)

/-- **Total number of nonattacking anassas on the square board.** For natural numbers $m$ and
$k$ and each $p$, let $A_S(m, k, p)$ be the number of nonattacking placements of $k$ anassas on
the square board $[1, m]^2$ with exactly $p$ of them strictly below the main diagonal, that is,
the number of $k$-element sets of squares $(i, j) \in [1, m]^2$ in which no two squares have
the same $i$ or the same $i - j$ and exactly $p$ squares satisfy $j < i$. Then, in $\mathbb{Q}$,
$$
\sum_{p=0}^{k} A_S(m, k, p) = \sum_{j=0}^{\lceil k/2 \rceil} (m-k+j)_j
\left\{ {m \atop m-k+j} \right\} 2^{k-2j} \left( \binom{k-j}{j-1} + \binom{k-j+1}{j} \right),
$$
where $(x)_j = x(x-1) \cdots (x-j+1)$ is the falling factorial, $\binom{k-j}{-1} = 0$, the power
$2^{k-2j}$ has an integer exponent, and $\left\{ {n \atop i} \right\}$ is Knuth's extension of
the Stirling numbers of the second kind to integer arguments; since $m \ge 0$, here it is the
ordinary Stirling number when $m - k + j \ge 0$ and $0$ otherwise.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 13 (`jis-2025-25.8.6-thm-13`). -/
public theorem_wanted sum_anassasBelow_eq (m k : ℕ) :
    (∑ p ∈ range (k + 1), (anassasBelow m k p : ℚ)) =
      ∑ j ∈ range ((k + 1) / 2 + 1),
        (∏ t ∈ range j, ((m : ℚ) - k + j - t)) * extStirlingSecond m ((m : ℤ) - k + j) *
          (2 : ℚ) ^ ((k : ℤ) - 2 * j) *
          ((if j = 0 then 0 else ((k - j).choose (j - 1) : ℚ)) + ((k - j + 1).choose j : ℚ))

/-- **Polynomial formula for the number of nonattacking anassas.** For natural numbers $m$ and
$k$, let $A_S(m, k, p)$ be the number of nonattacking placements of $k$ anassas on the square
board $[1, m]^2$ with exactly $p$ of them strictly below the main diagonal, that is, the number
of $k$-element sets of squares $(i, j) \in [1, m]^2$ in which no two squares have the same $i$
or the same $i - j$ and exactly $p$ squares satisfy $j < i$. Then, in $\mathbb{Q}$,
$\sum_{p=0}^{k} A_S(m, k, p) = \sum_{d=0}^{2k} c_d m^d$ with
$$
c_d = \sum_{i=d}^{2k} \frac{(-1)^{i-d}}{i!} \left[ {i \atop d} \right]
\sum_{j=0}^{U(i,k)} \alpha(k, j) \sum_{p=L(i,k)}^{k-j} S_2(p+k-j, p)
\sum_{b=0}^{j} \binom{p}{b} \binom{k}{j-b} \binom{b}{k+p-i},
$$
where $\left[ {i \atop d} \right]$ is the unsigned Stirling number of the first kind, $S_2$ is
the 2-associated Stirling number of the second kind,
$\alpha(k, j) = 2^{k-2j} \left( \binom{k-j}{j-1} + \binom{k-j+1}{j} \right) j!$ with
$\binom{k-j}{-1} = 0$ and an integer exponent in $2^{k-2j}$,
$U(i, k) = \min(\lceil k/2 \rceil, 2k - i)$ and $L(i, k) = \max(0, i - k)$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 16 (`jis-2025-25.8.6-thm-16`). -/
public theorem_wanted sum_anassasBelow_eq_poly (m k : ℕ) :
    (∑ p ∈ range (k + 1), (anassasBelow m k p : ℚ)) =
      ∑ d ∈ range (2 * k + 1),
        (∑ i ∈ Icc d (2 * k), (-1) ^ (i - d) / (i.factorial : ℚ) * (Nat.stirlingFirst i d : ℚ) *
          ∑ j ∈ range (min ((k + 1) / 2) (2 * k - i) + 1),
            (2 : ℚ) ^ ((k : ℤ) - 2 * j) *
              ((if j = 0 then 0 else ((k - j).choose (j - 1) : ℚ)) + ((k - j + 1).choose j : ℚ)) *
              (j.factorial : ℚ) *
              ∑ p ∈ Icc (i - k) (k - j), (twoAssocStirlingSecond (p + k - j) p : ℚ) *
                ∑ b ∈ range (j + 1),
                  (p.choose b : ℚ) * (k.choose (j - b) : ℚ) * (b.choose (k + p - i) : ℚ)) *
          (m : ℚ) ^ d

end

end MetaMathlibExt
