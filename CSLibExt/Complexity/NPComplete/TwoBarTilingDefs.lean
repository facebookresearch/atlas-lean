/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILING A POLYGON WITH TWO BARS: definitions

Source:
D. Beauquier, M. Nivat, É. Rémila and M. Robson, "Tiling figures of the plane with two bars",
Computational Geometry 5(1) (1995), 1-25, doi:10.1016/0925-7721(94)00015-N;
T. Horiyama, T. Ito, K. Nakatsuka, A. Suzuki and R. Uehara, "Complexity of tiling a polygon
with trominoes or bars", Discrete and Computational Geometry 58(3) (2017), 686-704,
doi:10.1007/s00454-017-9884-9, Theorem 3 (2BAR-tiling).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoBarTiling

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

end MetaMathlibExt.Complexity.NPComplete.TwoBarTiling
