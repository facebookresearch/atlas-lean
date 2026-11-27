/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on graphs of thickness at most k (fixed k ≥ 2) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 ("SIMPLE MAX CUT becomes NP-hard
for k = 2 also (even if G is such that deleting a single vertex makes it planar) [7]", where [7]
is F. Barahona, "On the complexity of max cut", Report No. 186, Université Scientifique et
Médicale et Institut National Polytechnique de Grenoble (1980)) and Table 1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, comment ("Remains
NP-complete if `w(e) = 1` for all `e ∈ E` (the SIMPLE MAX CUT problem) [...], and if, in
addition, no vertex has degree exceeding 3 [Yannakakis, 1978b]");
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th Annual ACM
Symposium on Theory of Computing (1978), 253-264, doi:10.1145/800133.804355;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutThickness

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on graphs of thickness at most k is NP-complete

Fix an integer `k ≥ 2`.
INSTANCE: a graph `G = (V, E)` of thickness at most `k` and a positive integer `K`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that at least `K`
edges of `E` have one endpoint in `V₁` and one endpoint in `V₂`?

Johnson (1985) defines the thickness-`k` graphs as the "graphs `G = (V, E)` where `E` can be
partitioned into sets `E₁` through `E_k` such that `Gᵢ = (V, Eᵢ)` is planar, `1 ≤ i ≤ k`", for a
fixed `k`, and states that SIMPLE MAX CUT "becomes NP-hard for `k = 2`" (Barahona 1980; the
report was not available). For `k = 1` (planar graphs) the problem is polynomial ([ND16]), so
the theorem below is stated for `k ≥ 2`. De Figueiredo, de Melo, Sasaki and Silva (2022) cite
Yannakakis (1978) for this entry: SIMPLE MAX CUT stays NP-complete on graphs with no vertex of
degree exceeding 3 ([ND16]), and such graphs have thickness at most `2` (by Vizing's theorem
their edges can be colored with `4` colors; the edges of colors `1, 2` and of colors `3, 4` each
form a graph of maximum degree `2`, a disjoint union of paths and cycles, which is planar), so
those instances are instances of this problem for every fixed `k ≥ 2`. Membership in NP: the
certificate is the partition of `V` together with the partition `E₁, …, E_k`; the cut is counted
directly and each `Gᵢ` checked by a polynomial-time planarity test.

The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`CSLibExt.Complexity.NPComplete.MaxCutDefs`, whose question already counts edges), reused
here as in `SimpleMaxCutDegreeThreeWanted`, plus `0 < K` as in [ND16]. The restriction is that
the graph has thickness at most `k`: the question of GRAPH THICKNESS
(`GraphThickness.GraphThicknessFeasible` from
`WantedExt.Complexity.NPComplete.GraphThicknessWanted`) holds for the same vertex count and
edge list with the bound `k` (`withThickness`): the edges are split into `k` classes, each
spanning a planar subgraph on all vertices, with the shared straight-line planarity predicate
`SimpleGraph.IsPlanar` (by Fáry's theorem, planarity for finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n`, the edge list, and the bound `K`; this is the MAXIMUM
CUT instance type. -/
abbrev SimpleMaxCutThicknessInstance := MaxCutInstance

/-- The GRAPH THICKNESS instance with the same vertex count and edge list and the bound `k`. -/
def withThickness (k : ℕ) (i : SimpleMaxCutThicknessInstance) :
    GraphThickness.GraphThicknessInstance :=
  (i.1, i.2.1, k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: a well-formed MAXIMUM CUT
instance (a simple edge list on the vertices `0, ..., n - 1`) whose graph has thickness at most
`k`, and `0 < K`. -/
def WellFormed (k : ℕ) (i : SimpleMaxCutThicknessInstance) : Prop :=
  MaxCut.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (withThickness k i) ∧ 0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` with at least `K` edges between the two sets (the
MAXIMUM CUT question). -/
def SimpleMaxCutThicknessFeasible (i : SimpleMaxCutThicknessInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on graphs of thickness at most `k`, for the fixed `k`, as a decision problem
over bitstrings. -/
noncomputable def simpleMaxCutThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimpleMaxCutThicknessInstance) x with
  | some i => decide (WellFormed k i ∧ SimpleMaxCutThicknessFeasible i)
  | none => false

/-- **SIMPLE MAX CUT on graphs of thickness at most `k` is NP-complete for every fixed
`k ≥ 2`.** Source: Johnson (1985), Section 3 and Table 1 (Barahona 1980); Garey and Johnson
(1979), [ND16], comment; Yannakakis (1978). -/
public theorem_wanted simpleMaxCutThickness_npComplete (k : ℕ) (_hk : 2 ≤ k) :
    simpleMaxCutThicknessDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (simpleMaxCutThicknessDec k)

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutThickness
