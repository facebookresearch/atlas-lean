/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF MONOPOLAR GRAPHS is NP-complete

Source:
M. Barbato and D. Bezzi, "Monopolar graphs: complexity of computing classical graph
parameters", Discrete Applied Mathematics 291 (2021), 277-285, doi:10.1016/j.dam.2020.12.023
(Section 2.1, Proposition 2.8 in the authors' version: "The 3-Colorability problem on monopolar
graphs is NP-complete.");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "monopolar" (gc_1272),
problem 3-Colourability: NP-complete, with the reference to Barbato and Bezzi (2021).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ClusterDeletionWanted
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityMonopolar

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-!
# 3-COLORABILITY OF MONOPOLAR GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is monopolar. QUESTION: is `G`
properly 3-colorable, i.e., is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)` for every edge
`uv`?

This is GRAPH COLORING (`GraphColoringWanted`, [GT4]) with the bound fixed to `K = 3`, restricted
to monopolar graphs. Barbato and Bezzi: "A graph `G = (V, E)` is monopolar if `V` can be
partitioned into a stable set and a set inducing the union of vertex-disjoint cliques." The
stable set is a set `A` with Mathlib's `G.IsIndepSet A`; the rest `B = Aᶜ` induces (Mathlib's
`G.induce B`) a union of vertex-disjoint cliques, i.e. a cluster graph: every two distinct vertices
in the same connected component are adjacent, the predicate `ClusterDeletion.IsClusterGraph` of
`ClusterDeletionWanted`, reused here. Either part may be empty. Barbato and Bezzi prove
3-colorability NP-complete on monopolar graphs by adapting the reduction from 3-SAT; membership in
NP holds for all graphs.

The instance type is a vertex count and an edge list; `withThreeColors` pairs it with the bound
`3` to reuse GRAPH COLORING's graph (`Graph`, a simple graph on `Fin n`), well-formedness
(simple edge list) and question (`Colorable 3`), as in `ThreeColorabilityDiameterThreeWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ThreeColorabilityMonopolarInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH COLORING instance with the same graph and bound `K = 3`. -/
abbrev withThreeColors (i : ThreeColorabilityMonopolarInstance) : GraphColoringInstance :=
  (i.1, i.2, 3)

/-- `G` is monopolar: its vertex set splits into a stable set `A` and the rest `Aᶜ`, which induces a
union of vertex-disjoint cliques (a cluster graph). -/
def IsMonopolar {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A : Set (Fin n), G.IsIndepSet A ∧ ClusterDeletion.IsClusterGraph (G.induce Aᶜ)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (GRAPH
COLORING's well-formedness), and the graph is monopolar. -/
def WellFormed (i : ThreeColorabilityMonopolarInstance) : Prop :=
  GraphColoring.WellFormed (withThreeColors i) ∧ IsMonopolar (Graph (withThreeColors i))

/-- The graph is properly 3-colorable. -/
def ThreeColorabilityMonopolarFeasible (i : ThreeColorabilityMonopolarInstance) : Prop :=
  GraphColoringFeasible (withThreeColors i)

open Classical in
/-- 3-COLORABILITY OF MONOPOLAR GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityMonopolarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilityMonopolarInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilityMonopolarFeasible i)
  | none => false

/-- **3-COLORABILITY OF MONOPOLAR GRAPHS is NP-complete.** Source: Barbato and Bezzi (2021);
Garey and Johnson (1979), [GT4] (parent problem); ISGCI, class "monopolar". -/
public theorem_wanted threeColorabilityMonopolar_npComplete :
    threeColorabilityMonopolarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityMonopolarDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityMonopolar
