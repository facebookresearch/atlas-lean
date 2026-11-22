/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for graphs of thickness at most k is NP-complete, for every fixed k ≥ 1

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
NP-complete for `K = 3` and planar graphs with no vertex degree exceeding 4);
L. Stockmeyer, "Planar 3-colorability is polynomial complete", ACM SIGACT News 5(3) (1973),
19-25, doi:10.1145/1008293.1008294;
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (CHROMATIC NUMBER on thickness-`k` graphs: NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticNumber

/-!
# CHROMATIC NUMBER for graphs of thickness at most k is NP-complete, for every fixed k ≥ 1

Fix `k`. INSTANCE: a graph `G = (V, E)` of thickness at most `k` and a positive integer
`K ≤ |V|`. QUESTION: is the chromatic number of `G` at most `K`, i.e., is `G` `K`-colorable?

This is GRAPH K-COLORABILITY ([GT4], `GraphColoringWanted`) restricted to graphs of thickness at
most `k`. Planar graphs are exactly the graphs of thickness at most `1`, and GRAPH
K-COLORABILITY is NP-complete for `K = 3` on planar graphs (Stockmeyer 1973; the [GT4] comment).
A planar graph has thickness at most `k` for every `k ≥ 1` (put every edge in one class), so the
problem is NP-complete for every fixed `k ≥ 1`, which is the theorem below (one decision problem
per `k`). Johnson's Table 1 records the thickness-`k` entry (`k` fixed) as NP-complete.

The instance, its simple-edge-list conditions and the question are those of `GraphColoringWanted`
(`GraphColoring.GraphColoringInstance`: vertex count, edge list, `K`;
`GraphColoring.GraphColoringFeasible`: Mathlib's `SimpleGraph.Colorable K`). [GT4]'s bound
`0 < K ≤ |V|` is added to `WellFormed`.

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

/-- Well-formedness of an instance for the thickness bound `k`: a well-formed GRAPH K-COLORABILITY
instance (a simple edge list on `0, ..., n - 1`) whose graph has thickness at most `k`, with `0 < K
≤ n`. -/
def WellFormed (k : ℕ) (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (i.1, i.2.1, k) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CHROMATIC NUMBER for graphs of thickness at most `k`, as a decision problem over
bitstrings. -/
noncomputable def thicknessChromaticNumberDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed k i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **CHROMATIC NUMBER for graphs of thickness at most `k` is NP-complete, for every fixed `k ≥
1`.** Source: Garey and Johnson (1979), [GT4]; Stockmeyer (1973); Johnson (1985), Table 1. -/
public theorem_wanted thicknessChromaticNumber_npComplete (k : ℕ) (hk : 1 ≤ k) :
    thicknessChromaticNumberDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (thicknessChromaticNumberDec k)

end MetaMathlibExt.Complexity.NPComplete.ThicknessChromaticNumber
