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

/-- The cells of the Aztec diamond region of order `m`: the cell `(i, j)` is the unit square with
lower-left corner `(i, j)` and center `(i + 1/2, j + 1/2)`, and it lies in the region iff
`|i + 1/2| + |j + 1/2| ≤ m`. The Aztec diamond graph `AD_m` has these `2m(m + 1)` cells as vertices
and joins two cells when they share a side. -/
abbrev AztecCell (m : ℕ) : Type :=
  {c : ℤ × ℤ // |2 * c.1 + 1| + |2 * c.2 + 1| ≤ 2 * (m : ℤ)}

/-- Ciucu's `4 × 4` periodic weight matrix `A` of Section 7 (the display before (7.1)), whose two
zero entries delete edges of the Aztec diamond graph. -/
def ciucuMatrix : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 1, 1, 1; 1, 0, 1, 1; 0, 1, 1, 1; 1, 1, 1, 1]

/-- The row index, in the `2m × 2m` array formed by the centers of the edges of `AD_m`, of the edge
joining the cells `c` and `d`. With doubled center coordinates `X = c.1 + d.1 + 1` and
`Y = c.2 + d.2 + 1` of that edge, the array rows are the diagonals `X + Y = const`, numbered
`0, …, 2m - 1` by `(X + Y + 2m - 1) / 2`. -/
def edgeRow (m : ℕ) (c d : ℤ × ℤ) : ℤ :=
  ((c.1 + d.1 + 1) + (c.2 + d.2 + 1) + 2 * m - 1) / 2

/-- The column index of the edge joining `c` and `d` in the same array: the diagonals
`X - Y = const`, numbered `0, …, 2m - 1` by `(X - Y + 2m - 1) / 2`. -/
def edgeCol (m : ℕ) (c d : ℤ × ℤ) : ℤ :=
  ((c.1 + d.1 + 1) - (c.2 + d.2 + 1) + 2 * m - 1) / 2

/-- Ciucu's periodic weight `wt_A` (Definition 3.3) of the edge joining `c` and `d` in `AD_m`: the
entry of `A` in position `(row mod 4, column mod 4)` of the array of edge centers, i.e. `A` placed
in a corner of the array and repeated with period `4` in both directions. -/
def ciucuWeight (m : ℕ) (c d : ℤ × ℤ) : ℕ :=
  ciucuMatrix ⟨(edgeRow m c d % 4).toNat % 4, Nat.mod_lt _ (Nat.succ_pos 3)⟩
    ⟨(edgeCol m c d % 4).toNat % 4, Nat.mod_lt _ (Nat.succ_pos 3)⟩

/-- The graph of Ciucu's (7.1) for the Aztec dragon of order `n`: the spanning subgraph of the Aztec
diamond graph `AD_{2n}` keeping exactly the edges of weight `1` under `wt_A` (the edges of weight
`0` are deleted). Ciucu shows that its perfect matchings are equinumerous with the tilings of the
dragon `R_n`. -/
def dragonGraph (n : ℕ) : SimpleGraph (AztecCell (2 * n)) :=
  SimpleGraph.fromRel fun c d =>
    |c.1.1 - d.1.1| + |c.1.2 - d.1.2| = 1 ∧ ciucuWeight (2 * n) c.1 d.1 = 1

/-- Propp's Problem 15, in the form of Ciucu's (7.1) and Theorem 7.1 at `a = 1`: for every `n` the
number of perfect matchings of the Aztec diamond graph `AD_{2n}` with the periodic weight `wt_A`
(the dragon graph) is `2^{n(n+1)}`. -/
def aztecDragonCount : Prop :=
  ∀ n : ℕ, Nat.card {M : (dragonGraph n).Subgraph // M.IsPerfectMatching} = 2 ^ (n * (n + 1))

/--
Resolved true: Ciucu proves that the number of perfect matchings of the Aztec diamond graph AD_2n
with the periodic weight wt_A is 2^(n(n+1)) (Theorem 7.1 at a = 1) and, by his identification (7.1)
of these matchings with the tilings of the Aztec dragon R_n, that R_n has 2^(n(n+1)) tilings
(Corollary 7.2), as Propp's Problem 15 asks. Source: J. Propp, Twenty open problems in enumeration
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
