/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILING A POLYGON WITH TWO BARS is NP-complete

Source:
D. Beauquier, M. Nivat, É. Rémila and M. Robson, "Tiling figures of the plane with two bars",
Computational Geometry 5(1) (1995), 1-25, doi:10.1016/0925-7721(94)00015-N;
T. Horiyama, T. Ito, K. Nakatsuka, A. Suzuki and R. Uehara, "Complexity of tiling a polygon
with trominoes or bars", Discrete and Computational Geometry 58(3) (2017), 686-704,
doi:10.1007/s00454-017-9884-9, Theorem 3 (2BAR-tiling).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoBarTiling

/-!
# TILING A POLYGON WITH TWO BARS is NP-complete

Horiyama, Ito, Nakatsuka, Suzuki and Uehara (2017), Section 1: "A polyomino is a rectilinear
polygon (i.e., a polygon made by connecting unit squares along their edges.) Then, we study the
problem of tiling a rectilinear polygon with polyominoes, defined as follows: Given a
rectilinear polygon `P` and a set `S` of polyominoes, determine whether `P` can be covered
without any overlap using translated copies of polyominoes in `S`." The polygon may have holes,
and "`x × y`" is "the polyomino of a rectangle with `x` rows and `y` columns". Section 1.1.2:
"Beauquier et al. showed that the tiling problem is NP-complete even if `S = {1 × m, k × 1}`,
for any fixed integers `m ≥ 2` and `k ≥ 3`"; Horiyama et al. call this 2BAR-tiling and reprove
its NP-completeness (Theorem 3).

Fix integers `m ≥ 2` and `k ≥ 3`.
INSTANCE: a rectilinear polygon `P` made of unit squares, possibly with holes.
QUESTION: can `P` be covered without overlap by translated copies of the horizontal bar `1 × m`
and the vertical bar `k × 1`?

Representation. `P` is given by its unit cells `(x, y)` (`x` the column, `y` the row), a
nonempty duplicate-free list; the cells are connected along their edges, that is, the cell set
induces a connected subgraph of Mathlib's grid graph `hasse ℕ □ hasse ℕ` (cells adjacent when
they share an edge). Coordinates are natural numbers: tiling is invariant under translation and
every such polygon translates into the quadrant. A tiling is a list of placed bars whose cells,
counted with multiplicity, are a permutation of the cells of `P`: every cell of `P` is covered
exactly once and nothing outside `P` is covered.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the unit cells `(x, y)` of the polygon. -/
abbrev TwoBarTilingInstance := List (ℕ × ℕ)

/-- The grid graph on the unit cells of the quadrant: cells sharing an edge are adjacent. -/
abbrev CellGraph : SimpleGraph (ℕ × ℕ) := SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ

/-- Well-formedness: the polygon has at least one cell, no cell is listed twice, and its cells
are connected along their edges. -/
def WellFormed (i : TwoBarTilingInstance) : Prop :=
  i ≠ [] ∧ i.Nodup ∧ (CellGraph.induce {x | x ∈ i}).Connected

/-- The cells of the bar placed at `p`: the horizontal bar `1 × m`, cells `(x + t, y)` for
`t < m`, if `v = false`; the vertical bar `k × 1`, cells `(x, y + t)` for `t < k`, if
`v = true`. -/
def barCells (m k : ℕ) (v : Bool) (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  if v then (List.range k).map fun t => (p.1, p.2 + t)
  else (List.range m).map fun t => (p.1 + t, p.2)

/-- The polygon is tiled by the bars `1 × m` and `k × 1`: some placed bars (an orientation and a
position each) cover every cell of the polygon exactly once and nothing else. -/
def TwoBarTilingFeasible (m k : ℕ) (i : TwoBarTilingInstance) : Prop :=
  ∃ bs : List (Bool × (ℕ × ℕ)), (bs.flatMap fun t => barCells m k t.1 t.2).Perm i

open Classical in
/-- TILING A POLYGON WITH THE BARS `1 × m` AND `k × 1` as a decision problem over bitstrings. -/
noncomputable def twoBarTilingDec (m k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoBarTilingInstance) x with
  | some i => decide (WellFormed i ∧ TwoBarTilingFeasible m k i)
  | none => false

/-- **TILING A POLYGON WITH TWO BARS is NP-complete** for every fixed `m ≥ 2` and `k ≥ 3`.
Source: Beauquier, Nivat, Rémila and Robson (1995); Horiyama, Ito, Nakatsuka, Suzuki and Uehara
(2017), Theorem 3. -/
public theorem_wanted twoBarTiling_npComplete (m k : ℕ) (hm : 2 ≤ m) (hk : 3 ≤ k) :
    twoBarTilingDec m k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (twoBarTilingDec m k)

end MetaMathlibExt.Complexity.NPComplete.TwoBarTiling
