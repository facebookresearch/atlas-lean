/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE CONSTRAINED SUBGRAPH is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
145-159, doi:10.1016/0196-6774(85)90025-2, problem [4] DEGREE CONSTRAINED SUBGRAPH (reference:
Plesník and Wawruch; transformation from EXACT COVER BY 3-SETS);
J. Plesník and A. Wawruch, "On the complexity of finding degree constrained subgraphs", Acta
Math. Universitatis Comenianae 40 (1982), 215-218, as cited by the column (not available);
G. Gutin, E. J. Kim, A. Soleimanfallah, S. Szeider and A. Yeo, "Parameterized complexity results
for general factors in bipartite graphs with an application to constraint programming",
Algorithmica 64 (2012), 112-125, doi:10.1007/s00453-011-9548-8 (the NP-hard GENERAL FACTOR
problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSubgraph

/-!
# DEGREE CONSTRAINED SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and, for each vertex `v ∈ V`, a set `D_v` of allowable degrees.
QUESTION: does `G` contain a subgraph `G'` such that, if `d(v)` is the degree of vertex `v` in
`G'` for all `v ∈ V`, then `d(v) ∈ D_v` for all `v ∈ V`?

This is also the GENERAL FACTOR problem: is there a set `F ⊆ E` of edges such that every vertex
`v` is incident with a number of edges of `F` in its allowed set (Gutin et al. take the allowed
set inside `{0, ..., deg_G(v)}`; larger allowed degrees can never be met, so they change no
answer).

The graph is given by the list of the allowed sets, one per vertex (the number of vertices
`n = |V|` is its length, vertices `0, ..., n - 1`), each set a list without repetitions, and a
simple edge list on `Fin n`. The subgraph `G'` contains every vertex, since `d(v)` is required
for all `v ∈ V`: it is a spanning subgraph `H ≤ G`, and degrees are Mathlib's
`SimpleGraph.degree`.

Membership in NP: the edge set of `H`, a sublist of the edge list, is the certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the allowed degree sets `D_0, ..., D_{n-1}` (one list per vertex) and the edge
list. -/
abbrev DegreeConstrainedSubgraphInstance := List (List ℕ) × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`, `n` the number of allowed sets. -/
def Graph (i : DegreeConstrainedSubgraphInstance) : SimpleGraph (Fin i.1.length) :=
  Cslib.Complexity.Karp.edgeGraph i.1.length i.2

/-- Well-formedness of an instance: each allowed set is a list without repetitions, and the
edge list describes a simple graph on `0, ..., n - 1` (no duplicate edges in either
orientation, no self-loops, endpoints in range). -/
def WellFormed (i : DegreeConstrainedSubgraphInstance) : Prop :=
  (∀ D ∈ i.1, D.Nodup) ∧
    i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

open Classical in
/-- Some spanning subgraph `H ≤ G` gives every vertex `v` a degree in `D_v`. -/
def DegreeConstrainedSubgraphFeasible (i : DegreeConstrainedSubgraphInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1.length), H ≤ Graph i ∧ ∀ v, H.degree v ∈ i.1[v]

open Classical in
/-- DEGREE CONSTRAINED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def degreeConstrainedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DegreeConstrainedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ DegreeConstrainedSubgraphFeasible i)
  | none => false

/-- **DEGREE CONSTRAINED SUBGRAPH is NP-complete.** Source: Johnson, NP-completeness column
(1985), problem [4]; Plesník and Wawruch (1982); Gutin et al. (2012). -/
public theorem_wanted degreeConstrainedSubgraph_npComplete :
    degreeConstrainedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L degreeConstrainedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSubgraph
