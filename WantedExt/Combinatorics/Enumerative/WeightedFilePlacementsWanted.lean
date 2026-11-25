/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.WeightedFilePlacements

/-!
# Weighted file placements on singleton boards

Statements from Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24
(2024), Article A58. A Ferrers board is given by its weakly increasing list of column heights
`b = [b_1, …, b_n]`; cells are pairs `(column, row)`, both `0`-indexed, so column `i` holds the
rows `0, …, b_{i+1} - 1` and row `r` lies in level `r / m`. Polynomial identities are stated
for every integer `x`, which is equivalent for polynomials over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Goldman–Joichi–White factorization theorem.** Let $B = (b_1, \dots, b_n)$ be a Ferrers
board, that is $b_1 \le \dots \le b_n$, and let $r_k(B) = r_{k,1}(B)$ be the number of placements
of $k$ non-attacking rooks on $B$ (no two in the same row or column). Then for every integer $x$,
$$
\sum_{k=0}^{n} r_k(B)\, x\downarrow_{n-k} = \prod_{i=1}^{n} \bigl(x + b_i - (i-1)\bigr),
$$
where $x\downarrow_j = x(x-1)\cdots(x-j+1)$ is the falling factorial, the $m$-falling factorial
for $m = 1$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 1 (Goldman, Joichi and White) (`integers-2024-A58-thm-1`). -/
public theorem_wanted rookNumber_factorization (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber 1 b k : ℤ) * mFallingFactorial x (b.length - k) 1 =
      ∏ i ∈ Finset.range b.length, (x + b.getD i 0 - i)

/-- **Briggs–Remmel factorization on singleton boards.** Let $m \ge 1$ and let
$B = (b_1, \dots, b_n)$ be a singleton board for $m$. Then for every integer $x$,
$$
\sum_{k=0}^{n} r_{k,m}(B)\, x\downarrow_{n-k,m} = \prod_{i=1}^{n} \bigl(x + b_i - m(i-1)\bigr),
$$
where $r_{k,m}(B)$ is the $k$-th $m$-level rook number of $B$ and
$x\downarrow_{k,m} = x(x-m)\cdots(x-(k-1)m)$ is the $m$-falling factorial.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 2 (Briggs and Remmel) (`integers-2024-A58-thm-2`). -/
public theorem_wanted levelRookNumber_factorization_of_singleton (m : ℕ) (hm : 1 ≤ m)
    (b : List ℕ) (hb : IsSingletonBoard m b) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber m b k : ℤ) * mFallingFactorial x (b.length - k) m =
      ∏ i ∈ Finset.range b.length, (x + b.getD i 0 - m * i)

/-- **Zone factorization of the $m$-level rook polynomial.** Let $m \ge 1$ and let
$B = (b_1, \dots, b_n)$ be a Ferrers board, that is $b_1 \le \dots \le b_n$. Write
$\lfloor b \rfloor_m = m \lfloor b/m \rfloor$ for the largest multiple of $m$ that is at most $b$,
and $\rho_i = b_i - \lfloor b_i \rfloor_m$. The zone of column $i$ is the set $z$ of columns $k$
with $\lfloor b_k \rfloor_m = \lfloor b_i \rfloor_m$ (a maximal run of consecutive columns, since
the heights increase weakly), and $\rho_z = \sum_{k \in z} \rho_k$. Column $i$ is last in its zone
when $i = n$ or $\lfloor b_{i+1} \rfloor_m \ne \lfloor b_i \rfloor_m$. Let $\varepsilon_i = \rho_z$,
for $z$ the zone of $i$, if column $i$ is last in its zone, and $\varepsilon_i = 0$ otherwise.
Then for every integer $x$,
$$
\sum_{k=0}^{n} r_{k,m}(B)\, x\downarrow_{n-k,m} =
\prod_{i=1}^{n} \bigl(x + \lfloor b_i \rfloor_m - m(i-1) + \varepsilon_i\bigr),
$$
where $r_{k,m}(B)$ is the $k$-th $m$-level rook number of $B$ and
$x\downarrow_{k,m} = x(x-m)\cdots(x-(k-1)m)$ is the $m$-falling factorial.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 3 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-3`). -/
public theorem_wanted levelRookNumber_factorization_zones (m : ℕ) (hm : 1 ≤ m) (b : List ℕ)
    (hb : b.Pairwise (· ≤ ·)) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber m b k : ℤ) * mFallingFactorial x (b.length - k) m =
      ∏ i ∈ Finset.range b.length,
        (x + (b.getD i 0 / m * m : ℕ) - m * i +
          if i + 1 = b.length ∨ b.getD (i + 1) 0 / m ≠ b.getD i 0 / m then
            ∑ k ∈ (Finset.range b.length).filter (fun k => b.getD k 0 / m = b.getD i 0 / m),
              ((b.getD k 0 % m : ℕ) : ℤ)
          else 0)

/-- **Level-number factorization of the $m$-level rook polynomial.** Let $m \ge 1$ and let
$B = (b_1, \dots, b_n)$ be a Ferrers board, that is $b_1 \le \dots \le b_n$, with $b_i \le mn$ for
every $i$. Number the rows from $0$ at the bottom, so that column $i$ has the cells in rows
$0, \dots, b_i - 1$, and for $1 \le j \le n$ let $l_j$ be the number of cells of $B$ whose row $r$
satisfies $\lfloor r/m \rfloor = n - j$ (the $j$-th level from the top). Then for every integer $x$,
$$
\sum_{k=0}^{n} r_{k,m}(B)\, x\downarrow_{n-k,m} = \prod_{j=1}^{n} \bigl(x + l_j - m(j-1)\bigr),
$$
where $r_{k,m}(B)$ is the $k$-th $m$-level rook number of $B$ and
$x\downarrow_{k,m} = x(x-m)\cdots(x-(k-1)m)$ is the $m$-falling factorial.

The bound $b_i \le mn$ makes $B$ lie in $n$ levels, as in the paper's setting; without it the
formula fails ($m = 1$, $B = (2)$).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 4 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-4`). -/
public theorem_wanted levelRookNumber_factorization_levels (m : ℕ) (hm : 1 ≤ m) (b : List ℕ)
    (hb : b.Pairwise (· ≤ ·)) (hbn : ∀ h ∈ b, h ≤ m * b.length) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber m b k : ℤ) * mFallingFactorial x (b.length - k) m =
      ∏ j ∈ Finset.range b.length,
        (x + ((ferrersBoardCells b).filter fun c => c.2 / m = b.length - 1 - j).card - m * j)

/-- **Weighted file numbers equal level rook numbers on singleton boards.** Let $m \ge 1$ and let
$B$ be a singleton board for $m$. Then for every $k \in \mathbb{N}$ the $k$-th $m$-weighted file
placement number of $B$ equals its $k$-th $m$-level rook number: $f_{k,m}(B) = r_{k,m}(B)$.

Equivalently, the $m$-weights of the file placements with $k$ cells that are not $m$-level rook
placements sum to $0$. The paper prints the corollary as the polynomial identity
$\sum_k f_{k,m}(B)\, x\downarrow_{n-k,m} = \sum_k r_{k,m}(B)\, x\downarrow_{n-k,m}$, where $n$ is
the number of columns and $x\downarrow_{j,m} = \prod_{i<j} (x - mi)$; it follows by summing, and the
paper derives it from this cancellation for each $k$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Corollary 6 and the sentence before it (`integers-2024-A58-cor-6`). -/
public theorem_wanted weightedFileNumber_eq_levelRookNumber_of_singleton (m : ℕ) (hm : 1 ≤ m)
    (b : List ℕ) (hb : IsSingletonBoard m b) (k : ℕ) :
    weightedFileNumber m b k = (levelRookNumber m b k : ℤ)

/-- **Weights cancel on a block with two rooks in the chosen level.** Let $m \ge 2$, let $B$ be a
singleton board for $m$, with rows numbered from $0$ and row $r$ in level $\lfloor r/m \rfloor$,
and let $F_0$ be a file placement on $B$. Let $l$ be the chosen level of $F_0$ (among the levels
holding at least two cells of $F_0$, one holding the fewest, the lowest on ties) and $c_0$ the
leftmost cell of $F_0$ in level $l$, and suppose that level $l$ holds exactly two cells of $F_0$.
Then the $m$-weights $\operatorname{wt}_m(F)$ of the file placements $F$ in the block $P(F_0)$
sum to $0$, where $P(F_0)$ consists of the file placements on $B$ that agree with $F_0$ outside
level $l$, use the same columns as $F_0$ inside level $l$, and contain $c_0$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Lemma 8 (`integers-2024-A58-lem-8`). -/
public theorem_wanted sum_filePlacementWeight_block_of_two (m : ℕ) (hm : 2 ≤ m) (b : List ℕ)
    (hb : IsSingletonBoard m b) (F₀ : Finset (ℕ × ℕ)) (hF₀ : F₀ ∈ filePlacements b)
    (l : ℕ) (c₀ : ℕ × ℕ) (hl : IsChosenLevelAndLeftmost m F₀ l c₀)
    (h2 : (F₀.filter fun c => c.2 / m = l).card = 2) :
    ∑ F ∈ filePlacementBlock m b F₀ l c₀, filePlacementWeight m F = 0

/-- **Cancellation of the weights over a block.** Let $m \ge 2$ and let $B$ be a singleton board
for $m$. Let $F_0$ be a file placement on $B$ that is not an $m$-level rook placement. Let $l$ be a
level and $c_0$ a cell such that $l$ holds at least two cells of $F_0$ and holds the fewest cells
of $F_0$ among all such levels (the lowest such level on ties), and $c_0$ is the leftmost cell of
$F_0$ in level $l$. Then the $m$-weights of the file placements in the block $P(F_0)$ determined
by $l$ and $c_0$ sum to $0$: $\sum_{F \in P(F_0)} \mathrm{wt}_m(F) = 0$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 9 (`integers-2024-A58-thm-9`). -/
public theorem_wanted sum_filePlacementWeight_block (m : ℕ) (hm : 2 ≤ m) (b : List ℕ)
    (hb : IsSingletonBoard m b) (F₀ : Finset (ℕ × ℕ)) (hF₀ : F₀ ∈ filePlacements b)
    (hF₀r : F₀ ∉ levelRookPlacements m b) (l : ℕ) (c₀ : ℕ × ℕ)
    (hl : IsChosenLevelAndLeftmost m F₀ l c₀) :
    ∑ F ∈ filePlacementBlock m b F₀ l c₀, filePlacementWeight m F = 0

end

end MetaMathlibExt
