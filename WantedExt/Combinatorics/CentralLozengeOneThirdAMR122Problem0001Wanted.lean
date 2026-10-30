/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The central lozenge of the 2n - 1, 2n, 2n - 1 hexagon (Propp, Problem 1)

J. Propp, Twenty open problems in enumeration of matchings, Problem 1: show that in the `2n - 1, 2n,
2n - 1` semiregular hexagon, the central location (consisting of the two innermost triangles) is
covered by a lozenge in exactly one-third of the tilings. (Equivalently: if one chooses a random
perfect matching of the dual graph, the probability that the central edge is contained in the
matching is exactly 1/3.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MathlibExt.Combinatorics.CentralLozengeOneThirdAMR122Problem0001Wanted

/-!
Source: J. Propp, Twenty open problems in enumeration of matchings (1998), arXiv:math/9801060,
Problem 1. UnsolvedMath record UM-00800330 (`AMR-122-0001`), dataset ulamai/UnsolvedMath v1.8.0.

The `a, b, c` semiregular hexagon has side lengths `a, b, c, a, b, c` (Propp); it is placed in the
triangular lattice with vertices `0, a e₁, a e₁ + b e₂, (a - c) e₁ + (b + c) e₂, -c e₁ + (b + c) e₂,
-c e₁ + c e₂`, and lozenge tilings are the perfect matchings (Mathlib's
`Subgraph.IsPerfectMatching`) of the dual honeycomb graph, the correspondence Propp states. For `a =
c = 2n - 1`, `b = 2n` the center `(2n - 1/2) e₂` is the midpoint of the edge shared by the upward
triangle `(0, 2n - 1)` and the downward triangle `(-1, 2n - 1)`, the two innermost triangles.
Checked by computation (Kasteleyn determinants): the encoding gives MacMahon's counts (2, 20, 490
tilings for the 1,1,1, 2,2,2 and 2,3,4 hexagons; 3, 4116, 3184461423 for n = 1, 2, 3) and the
central lozenge lies in exactly one third of the tilings for n = 1, …, 5.
-/

/-- A unit triangle of the triangular lattice spanned by `e₁ = (1, 0)` and `e₂ = (1/2, √3/2)`,
with lattice points `p(i, j) = i e₁ + j e₂`: `(i, j, false)` is the upward triangle with vertices
`p(i, j), p(i+1, j), p(i, j+1)` and `(i, j, true)` the downward triangle with vertices
`p(i+1, j), p(i, j+1), p(i+1, j+1)`. -/
abbrev LatticeTriangle := ℤ × ℤ × Bool

/-- The unit triangles of the semiregular hexagon with side lengths `a, b, c, a, b, c` and vertices
`0, a e₁, a e₁ + b e₂, (a - c) e₁ + (b + c) e₂, -c e₁ + (b + c) e₂, -c e₁ + c e₂`, i.e. the convex
region `0 ≤ j ≤ b + c, -c ≤ i ≤ a, 0 ≤ i + j ≤ a + b` in the coordinates `i e₁ + j e₂`: a triangle
lies in it iff its three vertices do. -/
def InHexagon (a b c : ℤ) : LatticeTriangle → Prop
  | (i, j, false) => 0 ≤ j ∧ j ≤ b + c - 1 ∧ -c ≤ i ∧ i ≤ a - 1 ∧ 0 ≤ i + j ∧ i + j ≤ a + b - 1
  | (i, j, true) => 0 ≤ j ∧ j ≤ b + c - 1 ∧ -c ≤ i ∧ i ≤ a - 1 ∧ -1 ≤ i + j ∧ i + j ≤ a + b - 2

/-- An upward and a downward unit triangle sharing an edge: the upward triangle `(i, j)` shares its
three edges with the downward triangles `(i, j)`, `(i - 1, j)` and `(i, j - 1)`. -/
def SharesEdge : LatticeTriangle → LatticeTriangle → Prop
  | (i, j, false), (i', j', true) =>
    (i', j') = (i, j) ∨ (i', j') = (i - 1, j) ∨ (i', j') = (i, j - 1)
  | _, _ => False

/-- The finite honeycomb graph dual to the dissection of the `a, b, c` hexagon into unit triangles:
vertices are the triangles of the hexagon, edges join triangles sharing an edge. Its perfect
matchings are the lozenge tilings of the hexagon (a lozenge is the union of the two triangles of a
matching edge). -/
def hexagonGraph (a b c : ℤ) : SimpleGraph {t : LatticeTriangle // InHexagon a b c t} :=
  SimpleGraph.fromRel fun s t => SharesEdge s.1 t.1

/-- Propp's Problem 1: in the `2n - 1, 2n, 2n - 1` semiregular hexagon, the central location (the
two innermost triangles, the upward triangle `(0, 2n - 1)` and the downward triangle
`(-1, 2n - 1)`, which share the edge whose midpoint is the center of the hexagon) is covered by a
lozenge in exactly one third of the lozenge tilings: three times the number of perfect matchings
containing that edge equals the number of all perfect matchings. -/
def centralLozengeOneThird : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    3 * Nat.card {M : (hexagonGraph (2 * n - 1) (2 * n) (2 * n - 1)).Subgraph //
        M.IsPerfectMatching ∧ ∀ s t, s.1 = (0, 2 * (n : ℤ) - 1, false) →
          t.1 = (-1, 2 * (n : ℤ) - 1, true) → M.Adj s t} =
      Nat.card {M : (hexagonGraph (2 * n - 1) (2 * n) (2 * n - 1)).Subgraph // M.IsPerfectMatching}

/--
Resolved true (Ciucu–Krattenthaler; Helfgott–Gessel, as recorded in Propp's progress report): for
every `n ≥ 1` the central lozenge of the `2n - 1, 2n, 2n - 1` hexagon occurs in exactly one third of
its lozenge tilings. Source: J. Propp, Twenty open problems in enumeration of matchings (1998),
arXiv:math/9801060, Problem 1; resolution: M. Ciucu and C. Krattenthaler, The number of centered
lozenge tilings of a symmetric hexagon, J. Combin. Theory Ser. A 86 (1999), 103-126; H. Helfgott and
I. M. Gessel, Enumeration of tilings of diamonds and hexagons with defects, Electron. J. Combin. 6
(1999), R16; as recorded by J. Propp, Enumeration of matchings: problems and progress, in New
Perspectives in Algebraic Combinatorics, MSRI Publ. 38 (1999), arXiv:math/9904150, Propp's progress
note on Problem 1: 'Two independent and very different solutions of this problem have been found;
one by Mihai Ciucu and Christian Krattenthaler and the other by Harald Helfgott and Ira Gessel';
Ciucu-Krattenthaler count the rhombus tilings of the hexagon with sides a, a, b, a, a, b containing
the central unit rhombus (a, b of opposite parity), and 'the special case a = 2n - 1, b = 2n solves
Problem 1', https://arxiv.org/abs/math/9904150.
-/
public theorem_wanted centralLozengeOneThird_holds : centralLozengeOneThird

end MathlibExt.Combinatorics.CentralLozengeOneThirdAMR122Problem0001Wanted
