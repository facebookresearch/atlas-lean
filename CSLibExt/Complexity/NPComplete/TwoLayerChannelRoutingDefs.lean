/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fin.VecNotation

/-!
# TWO-LAYER CHANNEL ROUTING: definitions

INSTANCE: a positive integer `W`, a set of grid points
`P = {(aᵢ, W) : 1 ≤ i ≤ p} ∪ {(bⱼ, 0) : 1 ≤ j ≤ q}`, and a partition of `P` into nets
`N₁, ..., Nₘ`. QUESTION: is there a (reserved layer) two-layer channel routing for the nets, i.e.,
a set of grid segments `S = T₁ ∪ ... ∪ Tₘ` where all the grid segments in `S` are included in
the region between the lines `y = 0` and `y = W` (with none from those two lines), (2) for each
`i`, the segments in `Tᵢ` make up a tree whose leaves are the points in net `Nᵢ`, and (3) no two
trees `Tᵢ` and `Tⱼ` have any non-orthogonal intersections?

The grid is the hypercubic lattice `StatMech.Lattice.hypercubicLattice 2` on `ℤ²` from
`MathlibExt` (as in `PlanarInterconnectionGridWanted`), whose edges, the grid segments, join
points at `ℓ¹` distance 1; a point `v` has `x`-coordinate `v 0` and `y`-coordinate `v 1`. Each
`Tᵢ` is a finite subgraph of the lattice whose underlying graph is a tree (`SimpleGraph.IsTree`)
and whose leaves, the vertices with at most one neighbor in `Tᵢ`, are exactly the points of `Nᵢ`
(a net with one point is routed by the one-vertex tree on it). A segment is horizontal when its
ends have the same `y`-coordinate and vertical otherwise. In the reserved-layer model of the
column one layer carries the horizontal segments and the other the vertical ones, and changes of
direction happen only at grid points, so two trees may meet only in orthogonal intersections,
which the column defines as "a common point that joins two vertical grid segments in one pattern
and two horizontal segments in the other": at every common point one tree has exactly its two
vertical segments and the other exactly its two horizontal segments. Doglegs (several horizontal
segments of one net on different tracks) are allowed.

`W` is encoded in binary. Each `x`-coordinate is an integer, encoded as a pair of naturals
`(positive part, negative part)` representing their difference, as in `ZeroOneILPWanted`. The
partition is given by a net label `k < m` on each point of `P`; every label is used, since the
blocks of a partition are non-empty.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395,
doi:10.1016/0196-6774(82)90032-3, problem [8] TWO-LAYER CHANNEL ROUTING (reference: Szymanski;
transformation from 3SAT), with properties (2) and (3) from problem [7] TWO-LAYER MULTIPLE
MODULE ROUTING and the reserved-layer model from Section 2;
T. G. Szymanski, "Dogleg channel routing is NP-complete", IEEE Transactions on Computer-Aided
Design of Integrated Circuits and Systems 4 (1985), 31-41, doi:10.1109/TCAD.1985.1270096.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoLayerChannelRouting

/-- An instance: the channel width `W`, the number `m` of nets, the upper terminals `(aᵢ, W)`
and the lower terminals `(bⱼ, 0)`, each given by its `x`-coordinate (as positive part, negative
part) and its net label. -/
abbrev TwoLayerChannelRoutingInstance :=
  ℕ × ℕ × List ((ℕ × ℕ) × ℕ) × List ((ℕ × ℕ) × ℕ)

/-- The integer an encoded coordinate stands for. -/
def toInt (a : ℕ × ℕ) : ℤ := (a.1 : ℤ) - a.2

/-- The labeled grid points of `P`: `((aᵢ, W), k)` for the upper and `((bⱼ, 0), k)` for the
lower terminals, `k` being the terminal's net. -/
def terminals (i : TwoLayerChannelRoutingInstance) : List (StatMech.Lattice.Site 2 × ℕ) :=
  i.2.2.1.map (fun e => (![toInt e.1, (i.1 : ℤ)], e.2)) ++
    i.2.2.2.map (fun e => (![toInt e.1, 0], e.2))

/-- Well-formedness of an instance: `W` is positive, the upper terminals have distinct
`x`-coordinates and so do the lower ones (so `P` is a set of distinct points), every net label
is below `m`, and every net is non-empty. -/
def WellFormed (i : TwoLayerChannelRoutingInstance) : Prop :=
  0 < i.1 ∧ (i.2.2.1.map fun e => toInt e.1).Nodup ∧ (i.2.2.2.map fun e => toInt e.1).Nodup ∧
    (∀ e ∈ terminals i, e.2 < i.2.1) ∧ ∀ k < i.2.1, ∃ e ∈ terminals i, e.2 = k

/-- `v` is a leaf of `T`: a vertex of `T` with at most one neighbor in `T`. -/
def IsLeaf (T : (StatMech.Lattice.hypercubicLattice 2).Subgraph)
    (v : StatMech.Lattice.Site 2) : Prop :=
  v ∈ T.verts ∧ ∀ u w, T.Adj v u → T.Adj v w → u = w

/-- `T` runs horizontally through `v`: two different segments of `T` meet at `v`, and every
segment of `T` at `v` is horizontal (so `T` has exactly the two horizontal segments at `v`). -/
def RunsHorizontally (T : (StatMech.Lattice.hypercubicLattice 2).Subgraph)
    (v : StatMech.Lattice.Site 2) : Prop :=
  (∃ u w, u ≠ w ∧ T.Adj v u ∧ T.Adj v w) ∧ ∀ u, T.Adj v u → u 1 = v 1

/-- `T` runs vertically through `v`: two different segments of `T` meet at `v`, and every
segment of `T` at `v` is vertical (so `T` has exactly the two vertical segments at `v`). -/
def RunsVertically (T : (StatMech.Lattice.hypercubicLattice 2).Subgraph)
    (v : StatMech.Lattice.Site 2) : Prop :=
  (∃ u w, u ≠ w ∧ T.Adj v u ∧ T.Adj v w) ∧ ∀ u, T.Adj v u → u 0 = v 0

/-- The grid segment `uv` lies in the region `0 ≤ y ≤ W` and not on the line `y = 0` or the
line `y = W`. -/
def InChannel (W : ℕ) (u v : StatMech.Lattice.Site 2) : Prop :=
  0 ≤ u 1 ∧ u 1 ≤ W ∧ 0 ≤ v 1 ∧ v 1 ≤ W ∧ ¬ (u 1 = v 1 ∧ (u 1 = 0 ∨ u 1 = W))

/-- Some trees `T₀, ..., Tₘ₋₁` route the nets: each `Tₖ` is a finite tree in the grid whose
leaves are exactly the points of net `k`, every segment lies inside the channel, and two
different trees meet only in orthogonal intersections. -/
def TwoLayerChannelRoutingFeasible (i : TwoLayerChannelRoutingInstance) : Prop :=
  ∃ T : Fin i.2.1 → (StatMech.Lattice.hypercubicLattice 2).Subgraph,
    (∀ k, (T k).verts.Finite ∧ (T k).coe.IsTree ∧
      ∀ v, IsLeaf (T k) v ↔ (v, (k : ℕ)) ∈ terminals i) ∧
    (∀ k u v, (T k).Adj u v → InChannel i.1 u v) ∧
    ∀ k l, k ≠ l → ∀ v ∈ (T k).verts, v ∈ (T l).verts →
      (RunsVertically (T k) v ∧ RunsHorizontally (T l) v) ∨
        (RunsHorizontally (T k) v ∧ RunsVertically (T l) v)

open Classical in
/-- TWO-LAYER CHANNEL ROUTING as a decision problem over bitstrings. -/
noncomputable def twoLayerChannelRoutingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoLayerChannelRoutingInstance) x with
  | some i => decide (WellFormed i ∧ TwoLayerChannelRoutingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoLayerChannelRouting
