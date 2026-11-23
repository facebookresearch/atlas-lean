/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-COLORABILITY OF TRIANGLE-FREE GRAPHS is NP-complete for every fixed K ≥ 3

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
F. Maffray and M. Preissmann, "On the NP-completeness of the k-colorability problem for
triangle-free graphs", Discrete Mathematics 162 (1996), 313-317,
doi:10.1016/S0012-365X(97)89267-9;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66,
doi:10.55016/ojs/cdm.v2i1.61890, Theorem 2.3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangleFreeKColorability

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# K-COLORABILITY OF TRIANGLE-FREE GRAPHS is NP-complete for every fixed K ≥ 3

Fix an integer `K ≥ 3`.
INSTANCE: a finite simple undirected graph `G = (V, E)` that contains no triangle.
QUESTION: is `G` properly `K`-colorable, that is, is there a map `f : V → {1, …, K}` with
`f(u) ≠ f(v)` whenever `{u, v} ∈ E`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with the number of
colors fixed to `K` and the graphs restricted to triangle-free ones. Maffray and Preissmann
established NP-completeness of `K`-colorability for triangle-free graphs (for `K = 3` already on
triangle-free graphs of maximum degree 4). Kamiński and Lozin, Theorem 2.3, prove that vertex
`K`-colorability is NP-hard in the class of graphs of girth at least `g`, for all `K, g ≥ 3`; for
`g = 4` this is the class of triangle-free graphs, and they cite Maffray and Preissmann as the
earlier result on this topic. Membership in NP is immediate (a coloring is a certificate).

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable i.2.2`).
The restriction adds to well-formedness that the number of colors in the instance is the fixed
`K`, and that the graph is triangle-free: Mathlib's `SimpleGraph.CliqueFree 3` (no 3-clique).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed number of colors `k`: a well-formed GRAPH
K-COLORABILITY instance whose number of colors is `k` and whose graph is triangle-free (has no
3-clique). -/
def WellFormed (k : ℕ) (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = k ∧ (Graph i).CliqueFree 3

open Classical in
/-- K-COLORABILITY OF TRIANGLE-FREE GRAPHS, for the fixed number of colors `k`, as a decision
problem over bitstrings. -/
noncomputable def triangleFreeKColorabilityDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed k i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **K-COLORABILITY OF TRIANGLE-FREE GRAPHS is NP-complete for every fixed `K ≥ 3`.** Source:
Garey and Johnson (1979), [GT4]; Maffray and Preissmann (1996); Kamiński and Lozin (2007),
Theorem 2.3. -/
public theorem_wanted triangleFreeKColorability_npComplete (k : ℕ) (hk : 3 ≤ k) :
    triangleFreeKColorabilityDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (triangleFreeKColorabilityDec k)

end MetaMathlibExt.Complexity.NPComplete.TriangleFreeKColorability
