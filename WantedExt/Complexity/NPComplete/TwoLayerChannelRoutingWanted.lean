/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-LAYER CHANNEL ROUTING is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395,
doi:10.1016/0196-6774(82)90032-3, problem [8] TWO-LAYER CHANNEL ROUTING (reference: Szymanski;
transformation from 3SAT), with properties (2) and (3) from problem [7] TWO-LAYER MULTIPLE
MODULE ROUTING and the reserved-layer model from Section 2;
T. G. Szymanski, "Dogleg channel routing is NP-complete", IEEE Transactions on Computer-Aided
Design of Integrated Circuits and Systems 4 (1985), 31-41, doi:10.1109/TCAD.1985.1270096.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoLayerChannelRoutingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoLayerChannelRouting

/-!
# TWO-LAYER CHANNEL ROUTING is NP-complete

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

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-LAYER CHANNEL ROUTING is NP-complete.** Source: Johnson, NP-completeness column
(1982), problem [8]; Szymanski (1985). -/
public theorem_wanted twoLayerChannelRouting_npComplete :
    twoLayerChannelRoutingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoLayerChannelRoutingDec

end MetaMathlibExt.Complexity.NPComplete.TwoLayerChannelRouting
