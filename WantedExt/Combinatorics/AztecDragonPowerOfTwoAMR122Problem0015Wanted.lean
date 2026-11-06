/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tilings of the Aztec dragons (Propp, Problem 15)

J. Propp, Twenty open problems in enumeration of matchings, Problem 15: for the Aztec-type regions
in the dissection of the plane into equilateral triangles, squares and regular hexagons with 4
polygons meeting at each vertex, the number of (diform) tilings of the region of order `n` is
`2^(n(n+1))`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace MathlibExt.Combinatorics.AztecDragonPowerOfTwoAMR122Problem0015Wanted

/-!
Source: J. Propp, Twenty open problems in enumeration of matchings (1998), arXiv:math/9801060,
Problem 15. UnsolvedMath record UM-00800344 (`AMR-122-0015`), dataset ulamai/UnsolvedMath v1.8.0.

Propp and Ciucu give the dragon `R_n` only by a picture (Ciucu, Figure 7.1). Ciucu's (7.1)
identifies the tilings of `R_n` with the perfect matchings of the Aztec diamond graph `AD_(2n)`
under his periodic weight `wt_A` (Definition 3.3: the matrix `A` placed in a corner of the `2m × 2m`
array of edge centers of `AD_m` and repeated with period 4; edges of weight 0 are deleted), and the
statement is formalized in that form. `AD_m` has the cells `(i, j)` with `|2i + 1| + |2j + 1| ≤ 2m`
as vertices, adjacent when they share a side; the array of edge centers is indexed by the diagonals
`X + Y` and `X - Y` of the doubled edge centers. Since 4 divides the side `4n` of the array of
`AD_(2n)`, the eight ways of placing `A` in a corner give graphs related by symmetries of the
diamond. Checked by computation: the cell graph has the Aztec diamond counts `2^(m(m+1)/2)` for `m ≤
8`, the dragon graph has 4, 64, 4096 and 1048576 perfect matchings for `n = 1, …, 4` under all eight
placements, and a Lean `#eval` of the kept edges agrees with the checker for `n ≤ 4`. A
statement-local Aztec cell encoding exists in OpenConjectures (AztecDiamondHomomesy), which
WantedExt cannot import.
-/

/-- **Cells of the Aztec diamond.** For $m \in \mathbb{N}$, the cells of the Aztec diamond region of
order $m$ are the pairs of integers $(i, j)$ with $|2i + 1| + |2j + 1| \le 2m$. The pair $(i, j)$
stands for the unit square with lower-left corner $(i, j)$ and center $(i + \frac12, j + \frac12)$,
so the condition says that this center satisfies $|i + \frac12| + |j + \frac12| \le m$.

The Aztec diamond graph $AD_m$ has these $2m(m + 1)$ cells as vertices and joins two cells when
they share a side. -/
abbrev AztecCell (m : ℕ) : Type :=
  {c : ℤ × ℤ // |2 * c.1 + 1| + |2 * c.2 + 1| ≤ 2 * (m : ℤ)}

/-- **Ciucu's weight matrix for the Aztec dragon.** Ciucu's periodic weight matrix of Section 7 (the
display before (7.1)) is the $4 \times 4$ matrix with natural number entries, rows and columns
indexed by $0, 1, 2, 3$,

$$A = \begin{pmatrix}1 & 1 & 1 & 1\\1 & 0 & 1 & 1\\0 & 1 & 1 & 1\\1 & 1 & 1 & 1\end{pmatrix}.$$

Its two zero entries, in positions $(1, 1)$ and $(2, 0)$, delete edges of the Aztec diamond
graph. -/
def ciucuMatrix : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 1, 1, 1; 1, 0, 1, 1; 0, 1, 1, 1; 1, 1, 1, 1]

/-- **Row index of an edge of the Aztec diamond.** For $m \in \mathbb{N}$ and pairs of integers
$c = (c_1, c_2)$ and $d = (d_1, d_2)$, put $X = c_1 + d_1 + 1$ and $Y = c_2 + d_2 + 1$, the
doubled coordinates of the center of the edge joining $c$ and $d$. The row index of this edge is
$\lfloor (X + Y + 2m - 1) / 2 \rfloor$, so the rows of the $2m \times 2m$ array of edge centers of
the Aztec diamond graph $AD_m$ are the diagonals $X + Y = \mathrm{const}$, numbered
$0, \dots, 2m - 1$. -/
def edgeRow (m : ℕ) (c d : ℤ × ℤ) : ℤ :=
  ((c.1 + d.1 + 1) + (c.2 + d.2 + 1) + 2 * m - 1) / 2

/-- **Column index of an edge of the Aztec diamond.** For $m \in \mathbb{N}$ and pairs of integers
$c = (c_1, c_2)$ and $d = (d_1, d_2)$, put $X = c_1 + d_1 + 1$ and $Y = c_2 + d_2 + 1$, the
doubled coordinates of the center of the edge joining $c$ and $d$. The column index of this edge is
$\lfloor (X - Y + 2m - 1) / 2 \rfloor$, so the columns of the array of edge centers of the Aztec
diamond graph $AD_m$ are the diagonals $X - Y = \mathrm{const}$, numbered $0, \dots, 2m - 1$. -/
def edgeCol (m : ℕ) (c d : ℤ × ℤ) : ℤ :=
  ((c.1 + d.1 + 1) - (c.2 + d.2 + 1) + 2 * m - 1) / 2

/-- **Ciucu's periodic weight.** For $m \in \mathbb{N}$ and pairs of integers $c$ and $d$, let
$r$ and $s$ be the row and column indices of the pair $(c, d)$ in the array of edge centers of the
Aztec diamond graph $AD_m$. The weight $\mathrm{wt}_A(c, d)$ is the entry of Ciucu's matrix $A$ in
row $r \bmod 4$ and column $s \bmod 4$; that is, $A$ is placed in a corner of the array and
repeated with period $4$ in both directions (Ciucu's Definition 3.3). -/
def ciucuWeight (m : ℕ) (c d : ℤ × ℤ) : ℕ :=
  ciucuMatrix ⟨(edgeRow m c d % 4).toNat % 4, Nat.mod_lt _ (Nat.succ_pos 3)⟩
    ⟨(edgeCol m c d % 4).toNat % 4, Nat.mod_lt _ (Nat.succ_pos 3)⟩

/-- **The Aztec dragon graph.** For $n \in \mathbb{N}$, the dragon graph of order $n$ is the graph
on the cells of the Aztec diamond of order $2n$ in which two cells $c$ and $d$ are adjacent when
they share a side (their coordinates differ by $1$ in exactly one place) and the edge joining them
has weight $\mathrm{wt}_A(c, d) = 1$ under Ciucu's periodic weight. It is the spanning subgraph of
the Aztec diamond graph $AD_{2n}$ obtained by deleting the edges of weight $0$; Ciucu's (7.1)
shows that its perfect matchings are equinumerous with the tilings of the Aztec dragon $R_n$. -/
def dragonGraph (n : ℕ) : SimpleGraph (AztecCell (2 * n)) :=
  SimpleGraph.fromRel fun c d =>
    |c.1.1 - d.1.1| + |c.1.2 - d.1.2| = 1 ∧ ciucuWeight (2 * n) c.1 d.1 = 1

/-- **Propp's Aztec dragon count.** The statement that for every natural number $n$ the dragon
graph of order $n$ (the spanning subgraph of the Aztec diamond graph $AD_{2n}$ that keeps exactly
the edges of weight $1$ under Ciucu's periodic weight $\mathrm{wt}_A$) has exactly $2^{n(n+1)}$
perfect matchings. This is Propp's Problem 15 in the form of Ciucu's (7.1) and Theorem 7.1 at
$a = 1$. -/
def aztecDragonCount : Prop :=
  ∀ n : ℕ, Nat.card {M : (dragonGraph n).Subgraph // M.IsPerfectMatching} = 2 ^ (n * (n + 1))

/--
**Perfect matchings of the Aztec dragon graph (Ciucu, Wieland).** For every natural number $n$,
the dragon graph of order $n$ (the spanning subgraph of the Aztec diamond graph $AD_{2n}$ that
keeps exactly the edges of weight $1$ under Ciucu's periodic weight $\mathrm{wt}_A$) has exactly
$2^{n(n+1)}$ perfect matchings.

Ciucu proves that the number of perfect matchings of $AD_{2n}$ with the periodic weight
$\mathrm{wt}_A$ is $2^{n(n+1)}$ (Theorem 7.1 at $a = 1$) and, by his identification (7.1) of these
matchings with the tilings of the Aztec dragon $R_n$, that $R_n$ has $2^{n(n+1)}$ tilings
(Corollary 7.2), as Propp's Problem 15 asks.

Source: J. Propp, Twenty open problems in enumeration
of matchings (1998), arXiv:math/9801060, Problem 15; resolution: M. Ciucu, Perfect matchings and
perfect powers, J. Algebraic Combin. 17 (2003), 335-375, arXiv:math/0501521, Section 7 (The Aztec
dragon): (7.1) M(R_n) = M(AD_2n; wt_A) for the displayed 4 × 4 matrix A; Theorem 7.1, M(AD_2n; wt_B)
= (1 + a²)^(n(n+1)), where B at a = 1 is A; Corollary 7.2, T(R_n) = 2^(n(n+1)); Ciucu calls it an
ex-conjecture of Propp first proved by B. Wieland (unpublished; Propp's progress report
arXiv:math/9904150, Problem 15: 'Ben Wieland solved this problem'),
https://arxiv.org/abs/math/0501521.
-/
public theorem_wanted aztecDragonCount_holds : aztecDragonCount

end MathlibExt.Combinatorics.AztecDragonPowerOfTwoAMR122Problem0015Wanted
