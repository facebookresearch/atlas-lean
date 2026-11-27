/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for graphs of thickness at most k is NP-complete, for every fixed k ≥ 2

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN5] CHROMATIC INDEX (the
problem); I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (NP-complete for `K = 3` and cubic graphs); D. S. Johnson, "The
NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (CHROMATIC INDEX on thickness-`k` graphs: NP-complete,
citing Holyer).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.EdgeColoringWanted
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticIndex

/-!
# CHROMATIC INDEX for graphs of thickness at most k is NP-complete, for every fixed k ≥ 2

Fix `k`. INSTANCE: a graph `G = (V, E)` of thickness at most `k` and a positive integer `K`.
QUESTION: is the chromatic index of `G` at most `K`, i.e., can `E` be partitioned into at most
`K` sets none of which contains two edges with a common endpoint?

This is CHROMATIC INDEX ([OPEN5], `EdgeColoringWanted`) restricted to graphs of thickness at most
`k`. Holyer (1981) proves that deciding whether a cubic graph has chromatic index `3` is
NP-complete. A graph of maximum degree `3` has thickness at most `2`: by Vizing's theorem its
edges have a proper coloring with `4` colors, and the union of two color classes has maximum
degree at most `2`, hence is a disjoint union of paths and cycles and is planar; so the classes
`{1, 2}` and `{3, 4}` witness thickness at most `2`. Holyer's cubic instances therefore have
thickness at most `k` for every `k ≥ 2`, and the problem is NP-complete for every fixed `k ≥ 2`,
which is the theorem below (one decision problem per `k`). Johnson's Table 1 records the
thickness-`k` entry (`k` fixed) as NP-complete, citing Holyer. Thickness `1` (planar graphs) is
not claimed.

The instance, its simple-edge-list conditions and the question are those of `EdgeColoringWanted`
(`EdgeColoring.EdgeColoringInstance`: vertex count, edge list, `K`;
`EdgeColoring.EdgeColoringFeasible`: a color below `K` for every edge, different on any two edges
that share an endpoint). [OPEN5]'s positive `K` is added to `WellFormed`.

Thickness: a graph has thickness at most `k` when its edges can be partitioned into `k` classes
each spanning a planar subgraph on all the vertices. This is the question of `GraphThicknessWanted`
(GRAPH THICKNESS, Mansfield 1983) for the bound `k`, reused unchanged as
`GraphThickness.GraphThicknessFeasible (n, E, k)`: a map `f` from the edges to `Fin k` whose classes
`GraphThickness.edgeClass` each give a graph satisfying the shared planarity predicate
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's theorem, planarity of
finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the thickness bound `k`: a well-formed CHROMATIC INDEX
instance (a simple edge list on `0, ..., n - 1`) whose graph has thickness at most `k`, with `0 <
K`. -/
def WellFormed (k : ℕ) (i : EdgeColoring.EdgeColoringInstance) : Prop :=
  EdgeColoring.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (i.1, i.2.1, k) ∧ 0 < i.2.2

open Classical in
/-- CHROMATIC INDEX for graphs of thickness at most `k`, as a decision problem over
bitstrings. -/
noncomputable def thicknessChromaticIndexDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := EdgeColoring.EdgeColoringInstance) x with
  | some i => decide (WellFormed k i ∧ EdgeColoring.EdgeColoringFeasible i)
  | none => false

/-- **CHROMATIC INDEX for graphs of thickness at most `k` is NP-complete, for every fixed `k ≥ 2`.**
Source: Garey and Johnson (1979), [OPEN5]; Holyer (1981); Johnson (1985), Table 1. -/
public theorem_wanted thicknessChromaticIndex_npComplete (k : ℕ) (hk : 2 ≤ k) :
    thicknessChromaticIndexDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (thicknessChromaticIndexDec k)

end MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticIndex
