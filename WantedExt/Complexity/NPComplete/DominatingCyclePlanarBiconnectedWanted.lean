/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING CYCLE on planar 2-connected graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 3 (the DOMINATING SET [GT2] variant whose dominating
set must form a cycle: "NP-complete for planar 2-connected graphs, but solvable in polynomial
time for outerplanar graphs"), crediting
A. Proskurowski and M. M. Sysło, "Minimum dominating cycles in outerplanar graphs", Internat. J.
Comput. Inform. Sci. 10 (1981), 127-139, doi:10.1007/BF00977745 (not available);
H. Eto, H. Kawahara, E. Miyano and N. Nonoue, "Complexity of the minimum single dominating cycle
problem for graph classes", IEICE Trans. Inf. & Syst. E101-D (2018), 574-581,
doi:10.1587/transinf.2017FCP0007, Section 1 (the definition, and the hardness on planar graphs
attributed to Proskurowski and Sysło).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.CycleCover
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingCyclePlanarBiconnected

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING CYCLE on planar 2-connected graphs is NP-complete

INSTANCE: a planar 2-connected graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have a cycle `C` with at most `K` vertices whose vertex set dominates `G`,
i.e., every vertex of `G` lies on `C` or is adjacent to a vertex of `C`?

A dominating cycle is a cycle `C` with `V(G) = V(C) ∪ N(V(C))` (Eto, Kawahara, Miyano and Nonoue,
following Proskurowski and Sysło); the decision version asks for one with at most `K` vertices.
Johnson's column describes the same variant as the dominating set being "required to induce a
cycle"; the cycle need not be an induced subgraph, as in the definition above.

The instance, its graph and the simple-edge-list well-formedness are those of
`CSLibExt.Complexity.NPComplete.DominatingSetDefs` ([GT2]): vertices `Fin n`, a list of
distinct undirected edges without loops or repeated pairs, and the bound `K`. Planarity is the
repository's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's
theorem exists exactly for planar graphs), 2-connectivity the shared MathlibExt predicate
`SimpleGraph.IsVertexConnected 2` (more than two vertices, and connected after deleting any one
vertex), a cycle the MathlibExt structure `SimpleGraph.Cycle` (a closed walk with Mathlib's
`Walk.IsCycle`), and domination the MathlibExt predicate `SimpleGraph.IsDominating`. A cycle's
number of vertices is its length (`SimpleGraph.Cycle.length`, its number of edges), and its
vertex set is the support of its walk.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K` whose
graph is planar and 2-connected. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ (Graph i).IsPlanar ∧ (Graph i).IsVertexConnected 2

/-- Some cycle of at most `K` vertices dominates the graph. -/
def DominatingCycleFeasible (i : DominatingSetInstance) : Prop :=
  ∃ c : SimpleGraph.Cycle (Graph i), c.length ≤ i.2.2 ∧
    (Graph i).IsDominating {v | v ∈ c.walk.support}

open Classical in
/-- DOMINATING CYCLE on planar 2-connected graphs as a decision problem over bitstrings. -/
noncomputable def dominatingCyclePlanarBiconnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingCycleFeasible i)
  | none => false

/-- **DOMINATING CYCLE on planar 2-connected graphs is NP-complete.** Source: Johnson (1984),
DOMINATING SET [GT2]; Proskurowski and Sysło (1981); Eto, Kawahara, Miyano and Nonoue (2018). -/
public theorem_wanted dominatingCyclePlanarBiconnected_npComplete :
    dominatingCyclePlanarBiconnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingCyclePlanarBiconnectedDec

end MetaMathlibExt.Complexity.NPComplete.DominatingCyclePlanarBiconnected
