/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-LAYER MULTIPLE MODULE ROUTING is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395,
doi:10.1016/0196-6774(82)90032-3, problem [7] TWO-LAYER MULTIPLE MODULE ROUTING (reference:
T. G. Szymanski, "Dogleg channel routing is NP-complete", manuscript (1982); transformation from
3SAT) and the reserved-layer model of Section 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoLayerMultipleModuleRoutingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoLayerMultipleModuleRouting

open TwoLayerChannelRouting (toInt IsLeaf RunsVertically RunsHorizontally)

/-!
# TWO-LAYER MULTIPLE MODULE ROUTING is NP-complete

INSTANCE: a collection `{M₁, ..., Mₙ}` of non-intersecting modules (rectangles specified by
their four integer-coordinate corners), a set `P` of terminals (grid points on the perimeters of
the modules), a partition of `P` into nets `N₁, ..., Nₘ`, and an integer bound `B`.
QUESTION: is there a (reserved layer) routing for the nets that can be enclosed within a
rectangle of area `B`, i.e., a set of grid segments `S = T₁ ∪ ... ∪ Tₘ` and a rectangle `R` such
that (1) all the modules and all the grid segments in `S` are included in `R`, and none of the
grid segments is contained in any of the modules, (2) for each `i`, the segments in `Tᵢ` make up
a tree whose leaves are the points in net `Nᵢ`, and (3) no two trees `Tᵢ` and `Tⱼ` have any
non-orthogonal intersections?

The column states TWO-LAYER CHANNEL ROUTING ([8], `TwoLayerChannelRoutingDefs`) through
properties (2) and (3) of this problem, so this file reuses that file's grid, the hypercubic
lattice `StatMech.Lattice.hypercubicLattice 2` on `ℤ²` (a point `v` has `x`-coordinate `v 0` and
`y`-coordinate `v 1`), its leaves (`IsLeaf`), its orthogonal intersections (`RunsVertically`,
`RunsHorizontally`) and its integer coordinates (`toInt`). As there, each `Tᵢ` is a finite
subgraph of the lattice whose underlying graph is a tree and whose leaves are exactly the points
of `Nᵢ`, and two trees may meet only at a point where one has exactly its two vertical segments
and the other exactly its two horizontal segments.

Modules and the enclosing rectangle are axis-parallel rectangles, as in the column's Figure 1. A
module is given by its lower-left corner `(x₁, y₁)` and its upper-right corner `(x₂, y₂)`, with
`x₁ < x₂` and `y₁ < y₂`; its four corners are `(x₁, y₁)`, `(x₂, y₁)`, `(x₁, y₂)` and `(x₂, y₂)`,
and it is the closed region `x₁ ≤ x ≤ x₂`, `y₁ ≤ y ≤ y₂`. Two modules do not intersect when
their regions are disjoint. A grid segment is contained in a module when both of its ends lie in
the module's region (the region is convex), so a segment may leave a module's perimeter but never
run along it. The rectangle `R` is given by integer corners `(a₁, b₁)` and `(a₂, b₂)` and has area
`(a₂ - a₁) * (b₂ - b₁)`, which must be at most `B` (a routing fits in a rectangle of area `B`
exactly when it fits in one of area at most `B`, which can be enlarged); integer corners lose
nothing, since the modules and segments have integer coordinates and their bounding box lies
inside every enclosing axis-parallel rectangle. Coordinates are integers encoded as pairs of
naturals `(positive part, negative part)` as in `ZeroOneILPWanted`; `B` is encoded in binary.
The partition is given by a net label `k < m` on each terminal; every label is used, since the
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

/-- **TWO-LAYER MULTIPLE MODULE ROUTING is NP-complete.** Source: Johnson, NP-completeness
column (1982), problem [7], crediting Szymanski (1982). -/
public theorem_wanted twoLayerMultipleModuleRouting_npComplete :
    twoLayerMultipleModuleRoutingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoLayerMultipleModuleRoutingDec

end MetaMathlibExt.Complexity.NPComplete.TwoLayerMultipleModuleRouting
