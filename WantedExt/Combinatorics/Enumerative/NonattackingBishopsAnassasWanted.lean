/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Binomial
public import MathlibExt.Combinatorics.AssociatedStirlingSecond

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
  `{{n, k}}` are the canonical `twoAssocStirlingSecond` (integer-valued), and `Ring.choose` is the binomial coefficient with arbitrary
  top argument.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Nonattacking placements.** Let $B$ be a board, that is, a finite set of squares
$(i, j) \in \mathbb{Z}^2$, let $M$ be a list of basic moves $v \in \mathbb{Z}^2$, and let $k$ be a
natural number. The nonattacking placements of $k$ pieces with basic moves $M$ on $B$ are the
$k$-element subsets $S \subseteq B$ such that for all distinct squares $p, q \in S$ and every
move $v \in M$, the difference $q - p$ is not parallel to $v$, that is,
$(q_1 - p_1) v_2 \ne (q_2 - p_2) v_1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public def nonattackingPlacements (B : Finset (ℤ × ℤ)) (M : List (ℤ × ℤ)) (k : ℕ) :
    Finset (Finset (ℤ × ℤ)) :=
  (B.powersetCard k).filter fun S =>
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ v ∈ M, (q.1 - p.1) * v.2 ≠ (q.2 - p.2) * v.1

/-- **Exactly one nonattacking placement of no pieces.** For every board $B$, a finite set of
squares of $\mathbb{Z}^2$, and every list $M$ of basic moves in $\mathbb{Z}^2$, there is
exactly one nonattacking placement of $0$ pieces with basic moves $M$ on $B$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public theorem card_nonattackingPlacements_zero (B : Finset (ℤ × ℤ)) (M : List (ℤ × ℤ)) :
    (nonattackingPlacements B M 0).card = 1 := by
  simp [nonattackingPlacements, Finset.filter_singleton]

/-- **The square board.** For a natural number $m$, the square board $S_m$ is the set of squares
$(i, j) \in \mathbb{Z}^2$ with $1 \le i \le m$ and $1 \le j \le m$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2. -/
public def squareBoard (m : ℕ) : Finset (ℤ × ℤ) :=
  Icc (1 : ℤ) m ×ˢ Icc (1 : ℤ) m

/-- **White squares of the square board.** For a natural number $m$, the white squares of the
square board $S_m = [1, m]^2$ are the integer squares $(i, j) \in S_m$ for which $i + j$ is
even.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2, Table 1. -/
public def whiteSquares (m : ℕ) : Finset (ℤ × ℤ) :=
  (squareBoard m).filter fun s => Even (s.1 + s.2)

/-- **Black squares of the square board.** For a natural number $m$, the black squares of the
$m \times m$ board $S_m = [1, m]^2$ are the squares $(i, j) \in S_m$ with $i + j$ odd.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2, Table 1. -/
public def blackSquares (m : ℕ) : Finset (ℤ × ℤ) :=
  (squareBoard m).filter fun s => Odd (s.1 + s.2)

/-- **Basic moves of the bishop.** The basic moves of the bishop are the two vectors $(1, 1)$
and $(-1, 1)$ in $\mathbb{Z}^2$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2. -/
public def bishopMoves : List (ℤ × ℤ) := [(1, 1), (-1, 1)]

/-- **Basic moves of the anassa.** The basic moves of the anassa are the two vectors $(0, 1)$
and $(1, 1)$ in $\mathbb{Z}^2$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 3. -/
public def anassaMoves : List (ℤ × ℤ) := [(0, 1), (1, 1)]

/-- **Nonattacking bishops on a square board.** For natural numbers $m$ and $k$, $B_S(m, k)$ is the
number of ways to place $k$ nonattacking bishops on the $m \times m$ board $S_m = [1, m]^2$, that
is, the number of $k$-element subsets of $S_m$ no two of whose squares lie on a common line of
slope $1$ or $-1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.1. -/
public def bishopsSquare (m k : ℕ) : ℕ :=
  (nonattackingPlacements (squareBoard m) bishopMoves k).card

/-- **Nonattacking bishops on the white squares.** For natural numbers $m$ and $k$, $R_W(m, k)$ is
the number of $k$-element sets of white squares of the $m \times m$ board $S_m = [1, m]^2$ (the
squares $(i, j)$ with $i + j$ even) no two of which lie on a common line of slope $1$ or $-1$, that
is, the number of ways to place $k$ nonattacking bishops on the white squares of $S_m$.

In the source, $R_W(m, k)$ counts placements of $k$ nonattacking rooks on the white board $W_m$,
whose rows and columns are the diagonals of the white squares of $S_m$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.2. -/
public def bishopsWhite (m k : ℕ) : ℕ :=
  (nonattackingPlacements (whiteSquares m) bishopMoves k).card

/-- **Nonattacking bishops on the black squares.** For natural numbers $m$ and $k$, $R_K(m, k)$ is
the number of $k$-element sets of black squares of the $m \times m$ board $S_m = [1, m]^2$ (the
squares $(i, j)$ with $i + j$ odd) no two of which lie on a common line of slope $1$ or $-1$, that
is, the number of ways to place $k$ nonattacking bishops on the black squares of $S_m$.

In the source, $R_K(m, k)$ counts placements of $k$ nonattacking rooks on the black board $K_m$,
whose rows and columns are the diagonals of the black squares of $S_m$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.2. -/
public def bishopsBlack (m k : ℕ) : ℕ :=
  (nonattackingPlacements (blackSquares m) bishopMoves k).card

/-- **Nonattacking anassas by number below the diagonal.** For natural numbers $m$, $k$ and
$p$, $A_S(m, k, p)$ is the number of nonattacking placements of $k$ anassas on the square board
$S_m = \{1, \dots, m\}^2$ (that is, of $k$-element sets of squares of $S_m$ no two of which lie
on a common line in the direction $(0, 1)$ or $(1, 1)$) in which exactly $p$ of the squares
$(i, j)$ satisfy $j < i$, that is, lie strictly below the main diagonal.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 3.1. -/
public def anassasBelow (m k p : ℕ) : ℕ :=
  ((nonattackingPlacements (squareBoard m) anassaMoves k).filter fun S =>
    (S.filter fun s => s.2 < s.1).card = p).card

/-- **Extended Stirling numbers of the second kind.** Knuth's extended Stirling number of the
second kind at integers $n$ and $k$ is the natural number equal to the Stirling number of the
second kind $S(n, k)$ if $n \ge 0$ and $k \ge 0$, equal to the unsigned Stirling number of the
first kind $c(-k, -n)$ if $n < 0$ and $k < 0$, and equal to $0$ otherwise. Here $c(j, i)$ is the
number of permutations of $j$ elements with exactly $i$ cycles.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1 (extended Stirling numbers,
with the identity `{-j, -k} = [k, j]`). -/
public def extStirlingSecond (n k : ℤ) : ℕ :=
  if 0 ≤ n ∧ 0 ≤ k then Nat.stirlingSecond n.toNat k.toNat
  else if n < 0 ∧ k < 0 then Nat.stirlingFirst (-k).toNat (-n).toNat
  else 0

/-- **Extended Stirling numbers at natural arguments.** For all natural numbers $n$ and $k$, the
extended Stirling number of the second kind at $(n, k)$ equals the Stirling number of the second
kind $S(n, k)$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public theorem extStirlingSecond_natCast (n k : ℕ) :
    extStirlingSecond n k = Nat.stirlingSecond n k := by
  simp [extStirlingSecond]

/-- **Extended Stirling numbers at negative arguments.** For all positive integers $a$ and $b$,
the extended Stirling number of the second kind at $(-a, -b)$ equals the unsigned Stirling number
of the first kind $c(b, a)$, the number of permutations of $b$ elements with exactly $a$ cycles.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, proof of Theorem 2.2. -/
public theorem extStirlingSecond_neg_neg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    extStirlingSecond (-(a : ℤ)) (-(b : ℤ)) = Nat.stirlingFirst b a := by
  simp [extStirlingSecond, ha, hb, ha.ne', hb.ne']

/-- **Santos's coefficients.** For natural numbers $i$, $p$, $q$ and a complex number $z$,
Santos's coefficient $\beta_i(p, q, z)$ is the complex number
$$
\beta_i(p, q, z) = 2^{-2q} \sum_{b=\max(0, i-p)}^{q} 2^b \binom{2q-b}{q}
\sum_{a=0}^{b} \binom{p+b-q-z}{a} \binom{q+z}{b-a} \binom{a-q}{p+b-i},
$$
where $\binom{w}{n} = w(w-1)\cdots(w-n+1)/n!$ for complex $w$ and natural $n$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 2.7, equation (9). -/
public noncomputable def santosBeta (i p q : ℕ) (z : ℂ) : ℂ :=
  1 / 2 ^ (2 * q) *
    ∑ b ∈ Icc (i - p) q, 2 ^ b * ((2 * q - b).choose q : ℂ) *
      ∑ a ∈ range (b + 1),
        Ring.choose ((p : ℂ) + b - q - z) a * Ring.choose ((q : ℂ) + z) (b - a) *
          Ring.choose ((a : ℂ) - q) (p + b - i)

/-- **Santos's coefficient with all indices zero.** For every complex number $z$, Santos's
coefficient satisfies $\beta_0(0, 0, z) = 1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 2.7. -/
public theorem santosBeta_zero (z : ℂ) : santosBeta 0 0 0 z = 1 := by
  simp [santosBeta]

/-- **Constituent coefficients for bishops on one color.** For natural numbers $k$, $d$ and a
complex number $z$, the constituent coefficient $c_{k,d}(z)$ is
$$c_{k,d}(z) = \sum_{i=d}^{2k} \frac{(-1)^{i-d}}{i!} {i \brack d}
\sum_{p=\max(0, i-k)}^{k} \sum_{j=p}^{k} S_2(p+j, p) \, \beta_i(p+j, k-j, z),$$
where ${i \brack d}$ is the unsigned Stirling number of the first kind, $S_2(n, r)$ is the
2-associated Stirling number of the second kind, and $\beta_i(p, q, z)$ is the coefficient
$\beta$ of Santos's Lemma 2.7.

Taking $z = -\pi(m)$ and $z = \pi(m)$, where $\pi(m) \in \{0, 1\}$ is the parity of $m$, gives
the coefficients of $m^d$ in the quasi-polynomials (13) and (14) for $k$ bishops on the white
and black squares.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.8. -/
public noncomputable def bishopColorQuasiCoeff (k d : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Icc d (2 * k), (-1) ^ (i - d) / (i.factorial : ℂ) * (Nat.stirlingFirst i d : ℂ) *
    ∑ p ∈ Icc (i - k) k, ∑ j ∈ Icc p k,
      (twoAssocStirlingSecond (p + j) p : ℂ) * santosBeta i (p + j) (k - j) z

/-- **Constituent coefficient for no bishops.** For every complex number $z$, the constituent
coefficient $c_{0,0}(z)$ of the bishop quasi-polynomials (the case $k = d = 0$) equals $1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.8. -/
public theorem bishopColorQuasiCoeff_zero_zero (z : ℂ) : bishopColorQuasiCoeff 0 0 z = 1 := by
  simp [bishopColorQuasiCoeff, twoAssocStirlingSecond, santosBeta_zero]

/-! ## Collapsible boards -/

/-! Theorem 1.2 (`jis-2025-25.8.6-thm-2`) is not stated: see the audit table. -/

/-! ## The bishop -/

/-- **Arshon's formula for nonattacking bishops (Kotěšovec's form).** For all natural numbers $m$
and $k$, the number $B_S(m, k)$ of placements of $k$ nonattacking bishops on the $m \times m$
board satisfies

$$
B_S(m, k) = \sum_{j=0}^{m} \sum_{i=0}^{\lfloor (m+1)/2 \rfloor}
\binom{\lfloor (m+1)/2 \rfloor}{i} S\bigl(i + \lfloor m/2 \rfloor, m - j\bigr)
\sum_{l=0}^{\lfloor m/2 \rfloor} \binom{\lfloor m/2 \rfloor}{l}
S\bigl(l + \lfloor (m+1)/2 \rfloor, m - k + j\bigr),
$$

where, for integers $a \ge 0$ and $b$, $S(a, b)$ is the Stirling number of the second kind when
$b \ge 0$ and $0$ when $b < 0$ (Knuth's extended Stirling numbers of the second kind).

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 3 (Arshon, Kotěšovec)
(`jis-2025-25.8.6-thm-3`). -/
public theorem_wanted bishopsSquare_eq_arshon (m k : ℕ) :
    bishopsSquare m k =
      ∑ j ∈ range (m + 1), ∑ i ∈ range ((m + 1) / 2 + 1),
        ((m + 1) / 2).choose i * extStirlingSecond (i + m / 2 : ℕ) ((m : ℤ) - j) *
          ∑ l ∈ range (m / 2 + 1),
            (m / 2).choose l * extStirlingSecond (l + (m + 1) / 2 : ℕ) ((m : ℤ) - k + j)

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

/-- **Recurrence for bishops on the black squares.** Let $R_K(m, k)$ be the number of
nonattacking placements of $k$ bishops on the black squares $(i, j)$, with $i + j$ odd, of the
board $\{1, \dots, m\}^2$, and let $\pi(m) \in \{0, 1\}$ be the remainder of $m$ modulo $2$.
For $m, k \ge 1$,
$$R_K(m, k) = R_K(m-1, k) + (m - k + 1 - \pi(m)) \, R_K(m-1, k-1)$$
in the integers, and for every natural number $m$, $R_K(m, 0) = 1$ and $R_K(0, k) = 0$ for
$k \ge 1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsBlack_recurrence (m k : ℕ) :
    (bishopsBlack (m + 1) (k + 1) : ℤ) =
        bishopsBlack m (k + 1) + ((m : ℤ) - k + 1 - ((m + 1) % 2 : ℕ)) * bishopsBlack m k ∧
      bishopsBlack m 0 = 1 ∧ bishopsBlack 0 (k + 1) = 0

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

/-- **Extended Stirling formula for bishops on a square board.** For all natural numbers $m$ and
$k$, the number $B_S(m, k)$ of placements of $k$ nonattacking bishops on the $m \times m$ board
satisfies

$$
B_S(m, k) = \sum_{j=0}^{k} \sum_{i=0}^{j} \binom{\lfloor m/2 \rfloor}{i} S(m - i, m - j)
\sum_{l=0}^{k-j} \binom{\lceil m/2 \rceil}{l} S(m - l, m - k + j),
$$

where $S(a, b)$ is Knuth's extended Stirling number of the second kind for integers $a, b$: the
Stirling number of the second kind when $a, b \ge 0$, the unsigned Stirling number of the first
kind with arguments $-b, -a$ when $a, b < 0$, and $0$ otherwise.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 6 (`jis-2025-25.8.6-thm-6`). -/
public theorem_wanted bishopsSquare_eq_sum (m k : ℕ) :
    bishopsSquare m k =
      ∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1),
        (m / 2).choose i * extStirlingSecond ((m : ℤ) - i) ((m : ℤ) - j) *
          ∑ l ∈ range (k - j + 1),
            ((m + 1) / 2).choose l * extStirlingSecond ((m : ℤ) - l) ((m : ℤ) - k + j)

/-- **Ward's identity for Stirling numbers of the second kind.** For natural numbers $k \le m$,
$$S(m, m - k) = \sum_{p=0}^{k} S_2(k + p, p) \binom{m}{k + p},$$
where $S$ denotes the Stirling numbers of the second kind and $S_2$ the 2-associated Stirling
numbers of the second kind.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 8 (`jis-2025-25.8.6-lem-8`). -/
public theorem_wanted stirlingSecond_sub_eq_sum_associated (m k : ℕ) (hk : k ≤ m) :
    (Nat.stirlingSecond m (m - k) : ℤ) =
      ∑ p ∈ range (k + 1), twoAssocStirlingSecond (k + p) p * m.choose (k + p)

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

/-- **Recurrence for anassas below the diagonal.** Let $A(m, k, p)$ be the number of
nonattacking placements of $k$ anassas on the square board $\{1, \dots, m\}^2$ with exactly $p$
of them strictly below the main diagonal, let ${n \brace j}$ be Knuth's extended Stirling
numbers of the second kind, and let $\delta$ be the Kronecker delta. For $m \ge 1$, $k \ge 2$
and $p \ge 1$,
$$A(m, k, p) = A(m-1, k, p) + (m-k+1) A(m-1, k-1, p) + (m-p) A(m-1, k-1, p-1) +
(m-p)(m-k+1) A(m-1, k-2, p-1)$$
in the integers. Moreover, for all natural numbers $m$, $k$ and $p$,
$A(0, k, p) = \delta_{k0} \delta_{p0}$, $A(m, 0, p) = \delta_{p0}$,
$A(m, 1, p) = {m+1 \brace m} \delta_{p0} + {m \brace m-1} \delta_{p1}$ and
$A(m, k, 0) = {m+1 \brace m-k+1}$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 11 (`jis-2025-25.8.6-thm-11`). -/
public theorem_wanted anassasBelow_recurrence (m k p : ℕ) :
    ((anassasBelow (m + 1) (k + 2) (p + 1) : ℤ) =
        anassasBelow m (k + 2) (p + 1) + ((m : ℤ) - k) * anassasBelow m (k + 1) (p + 1) +
          ((m : ℤ) - p) * anassasBelow m (k + 1) p +
          ((m : ℤ) - p) * ((m : ℤ) - k) * anassasBelow m k p) ∧
      anassasBelow 0 k p = (if k = 0 ∧ p = 0 then 1 else 0) ∧
      anassasBelow m 0 p = (if p = 0 then 1 else 0) ∧
      anassasBelow m 1 p =
        (if p = 0 then Nat.stirlingSecond (m + 1) m else 0) +
          (if p = 1 then extStirlingSecond m ((m : ℤ) - 1) else 0) ∧
      anassasBelow m k 0 = extStirlingSecond (m + 1 : ℕ) ((m : ℤ) - k + 1)

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
