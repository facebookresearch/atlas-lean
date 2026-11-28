/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISTANCE-d CHROMATIC NUMBER (fixed d ≥ 2) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3(2)
(1982), 182-195, doi:10.1016/0196-6774(82)90018-9, problem DISTANCE-d CHROMATIC NUMBER;
S. T. McCormick, "Optimal approximation of sparse Hessians and its equivalence to a graph
coloring problem", Mathematical Programming 26(2) (1983), 153-171, doi:10.1007/BF02592052;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the case `d = 1`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DistanceDChromaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistanceDChromaticNumber

/-!
# DISTANCE-d CHROMATIC NUMBER (fixed d ≥ 2) is NP-complete

For a fixed integer `d ≥ 2`: INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a partition `V = V₁ ∪ ⋯ ∪ V_K` such that if `u` and `v` are distinct elements
of some set `Vᵢ` of the partition, then there is no path from `u` to `v` in `G` of length `d` or
less?

The partition is a map `c : V → Fin K` (the blocks `Vᵢ = c⁻¹ {i}`, some possibly empty; since
`K ≤ |V|`, a partition into fewer nonempty blocks can be refined to exactly `K` nonempty blocks
without breaking the condition). A path is a Mathlib `SimpleGraph.Walk` with `IsPath` (no
repeated vertex), and its length is the number of edges. Johnson's column: "NP-complete for any
fixed d ≥ 1. The case for d = 1 is ordinary CHROMATIC NUMBER; the cited reference [McCormick]
proves NP-completeness for all fixed d ≥ 2."

The instance type, the graph and the simple-edge-list condition are those of GRAPH
K-COLORABILITY (`GraphColoring.GraphColoringInstance`, `GraphColoring.Graph`,
`GraphColoring.WellFormed`); `WellFormed` adds the bounds `0 < K ≤ |V|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DISTANCE-d CHROMATIC NUMBER (fixed d ≥ 2) is NP-complete.** For every fixed `d ≥ 2`.
Source: Johnson (1982), NP-completeness column; McCormick (1983). -/
public theorem_wanted distanceDChromaticNumber_npComplete (d : ℕ) (_hd : 2 ≤ d) :
    distanceDChromaticNumberDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (distanceDChromaticNumberDec d)

end MetaMathlibExt.Complexity.NPComplete.DistanceDChromaticNumber
