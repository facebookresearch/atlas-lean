/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-LAYER CHANNEL ROUTING: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395,
doi:10.1016/0196-6774(82)90032-3, problem [8] TWO-LAYER CHANNEL ROUTING (reference: Szymanski;
transformation from 3SAT), with properties (2) and (3) from problem [7] TWO-LAYER MULTIPLE
MODULE ROUTING and the reserved-layer model from Section 2;
T. G. Szymanski, "Dogleg channel routing is NP-complete", IEEE Transactions on Computer-Aided
Design of Integrated Circuits and Systems 4 (1985), 31-41, doi:10.1109/TCAD.1985.1270096.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fin.VecNotation

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
