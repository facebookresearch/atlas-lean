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

/-- **Unit triangles of the triangular lattice.** Let $e_1 = (1, 0)$ and
$e_2 = (1/2, \sqrt{3}/2)$, and write $p(i, j) = i e_1 + j e_2$ for integers $i, j$. A unit
triangle is a triple $(i, j, d)$ of integers $i, j$ and a boolean $d$: for $d$ false it is the
upward triangle $(i, j)$ with vertices $p(i, j)$, $p(i + 1, j)$, $p(i, j + 1)$, and for $d$ true
it is the downward triangle $(i, j)$ with vertices $p(i + 1, j)$, $p(i, j + 1)$, $p(i + 1, j + 1)$.
-/
abbrev LatticeTriangle := ℤ × ℤ × Bool

/-- **Unit triangles of a semiregular hexagon.** Let $e_1 = (1, 0)$, $e_2 = (1/2, \sqrt{3}/2)$ and
$p(i, j) = i e_1 + j e_2$, and call the triangles with vertices $p(i, j), p(i + 1, j), p(i, j + 1)$
and $p(i + 1, j), p(i, j + 1), p(i + 1, j + 1)$ the upward and the downward unit triangle $(i, j)$.
For integers $a, b, c$, the upward unit triangle $(i, j)$ lies in the $a, b, c$ hexagon when
$0 \le j \le b + c - 1$, $-c \le i \le a - 1$ and $0 \le i + j \le a + b - 1$, and the downward
unit triangle $(i, j)$ lies in it when $0 \le j \le b + c - 1$, $-c \le i \le a - 1$ and
$-1 \le i + j \le a + b - 2$.

These are exactly the unit triangles whose three vertices lie in the region of points
$i e_1 + j e_2$ with $0 \le j \le b + c$, $-c \le i \le a$ and $0 \le i + j \le a + b$. For
$a, b, c \ge 0$ this region is the (possibly degenerate) semiregular hexagon with side lengths
$a, b, c, a, b, c$ and vertices $0$, $a e_1$, $a e_1 + b e_2$, $(a - c) e_1 + (b + c) e_2$,
$-c e_1 + (b + c) e_2$ and $-c e_1 + c e_2$. -/
def InHexagon (a b c : ℤ) : LatticeTriangle → Prop
  | (i, j, false) => 0 ≤ j ∧ j ≤ b + c - 1 ∧ -c ≤ i ∧ i ≤ a - 1 ∧ 0 ≤ i + j ∧ i + j ≤ a + b - 1
  | (i, j, true) => 0 ≤ j ∧ j ≤ b + c - 1 ∧ -c ≤ i ∧ i ≤ a - 1 ∧ -1 ≤ i + j ∧ i + j ≤ a + b - 2

/-- **Unit triangles sharing an edge.** The relation between unit triangles $s$ and $t$ that holds
exactly when $s$ is an upward triangle $(i, j)$ and $t$ is one of the downward triangles $(i, j)$,
$(i - 1, j)$ and $(i, j - 1)$. These are the three downward triangles that share an edge with
the upward triangle $(i, j)$; the relation never holds with $s$ downward or $t$ upward. -/
def SharesEdge : LatticeTriangle → LatticeTriangle → Prop
  | (i, j, false), (i', j', true) =>
    (i', j') = (i, j) ∨ (i', j') = (i - 1, j) ∨ (i', j') = (i, j - 1)
  | _, _ => False

/-- **Dual honeycomb graph of a hexagon.** For integers $a, b, c$, the dual graph of the $a, b, c$
hexagon is the simple graph whose vertices are the unit triangles lying in the $a, b, c$ hexagon,
two of them being adjacent when one is an upward unit triangle $(i, j)$ and the other is one of the
downward unit triangles $(i, j)$, $(i - 1, j)$ and $(i, j - 1)$, that is, when they share an edge.

Its perfect matchings are the lozenge tilings of the hexagon (a lozenge is the union of the two
triangles of a matching edge). -/
def hexagonGraph (a b c : ℤ) : SimpleGraph {t : LatticeTriangle // InHexagon a b c t} :=
  SimpleGraph.fromRel fun s t => SharesEdge s.1 t.1

/-- **Propp's central lozenge problem.** Let $e_1 = (1, 0)$ and $e_2 = (1/2, \sqrt{3}/2)$, write
$p(i, j) = i e_1 + j e_2$, and call the triangles with vertices $p(i, j), p(i + 1, j), p(i, j + 1)$
and $p(i + 1, j), p(i, j + 1), p(i + 1, j + 1)$ the upward and the downward unit triangle $(i, j)$.
The statement that for every integer $n \ge 1$, with $a = c = 2n - 1$ and $b = 2n$, in the
semiregular hexagon with side lengths $a, b, c, a, b, c$ and vertices $0$, $a e_1$,
$a e_1 + b e_2$, $(a - c) e_1 + (b + c) e_2$, $-c e_1 + (b + c) e_2$ and $-c e_1 + c e_2$, three
times the number of perfect matchings of the dual honeycomb graph of the hexagon (whose vertices
are the unit triangles inside the hexagon and whose edges join triangles sharing an edge) that
contain the edge joining the upward unit triangle $(0, 2n - 1)$ and the downward unit triangle
$(-1, 2n - 1)$ equals the number of all perfect matchings of that graph.

These two triangles are the innermost ones: the edge they share has the center of the hexagon as
its midpoint. Since perfect matchings of the dual graph are lozenge tilings, the statement says
that the central location is covered by a lozenge in exactly one third of the lozenge tilings. -/
def centralLozengeOneThird : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    3 * Nat.card {M : (hexagonGraph (2 * n - 1) (2 * n) (2 * n - 1)).Subgraph //
        M.IsPerfectMatching ∧ ∀ s t, s.1 = (0, 2 * (n : ℤ) - 1, false) →
          t.1 = (-1, 2 * (n : ℤ) - 1, true) → M.Adj s t} =
      Nat.card {M : (hexagonGraph (2 * n - 1) (2 * n) (2 * n - 1)).Subgraph // M.IsPerfectMatching}

/--
**The central lozenge lies in one third of the tilings.** Let $e_1 = (1, 0)$ and
$e_2 = (1/2, \sqrt{3}/2)$, write $p(i, j) = i e_1 + j e_2$, and call the triangles with vertices
$p(i, j), p(i + 1, j), p(i, j + 1)$ and $p(i + 1, j), p(i, j + 1), p(i + 1, j + 1)$ the upward and
the downward unit triangle $(i, j)$. For every integer $n \ge 1$, let $a = c = 2n - 1$ and
$b = 2n$, and consider the semiregular hexagon with side lengths $a, b, c, a, b, c$ and vertices
$0$, $a e_1$, $a e_1 + b e_2$, $(a - c) e_1 + (b + c) e_2$, $-c e_1 + (b + c) e_2$ and
$-c e_1 + c e_2$, and its dual honeycomb graph, whose vertices are the unit triangles inside the
hexagon and whose edges join triangles sharing an edge. Three times the number of perfect
matchings of this graph that contain the edge joining the upward unit triangle $(0, 2n - 1)$ and
the downward unit triangle $(-1, 2n - 1)$ equals the number of all its perfect matchings. These two
triangles are the innermost ones, so, since perfect matchings of the dual graph are lozenge
tilings, the central location of the hexagon is covered by a lozenge in exactly one third of its
lozenge tilings.

Resolved true by Ciucu and Krattenthaler and, independently, by Helfgott and Gessel.

Source: J. Propp, Twenty open problems in enumeration of matchings (1998),
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
