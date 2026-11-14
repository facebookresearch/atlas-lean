/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING BY CLIQUES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT17] COVERING BY
CLIQUES;
L. T. Kou, L. J. Stockmeyer, and C. K. Wong, "Covering edges by cliques with
regard to keyword conflicts and intersection graphs", Communications of the ACM
21 (1978), 135-139, doi:10.1145/359340.359346;
J. Orlin, "Contentment in graph theory: covering graphs with cliques",
Indagationes Mathematicae (Proceedings) 80 (1977), 406-424,
doi:10.1016/1385-7258(77)90055-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringByCliques

/-!
# COVERING BY CLIQUES is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: are there `k ≤ K`
subsets `V₁, ..., Vₖ` of `V` such that each `Vᵢ` induces a complete subgraph of `G` and such
that for each edge `{u, v} ∈ E` there is some `Vᵢ` that contains both `u` and `v`?

"Induces a complete subgraph" is Mathlib's `IsClique`. Under `WellFormed` the edge list has
one entry per edge, so its length is `|E|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev CoveringByCliquesInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CoveringByCliquesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : CoveringByCliquesInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- The edges are covered by at most `K` cliques: for some `k ≤ K` there are vertex sets
`S j`, `j : Fin k`, each a clique of the graph, such that every edge has both endpoints in some
`S j`. -/
def CoveringByCliquesFeasible (i : CoveringByCliquesInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ S : Fin k → Set (Fin i.1),
    (∀ j, (Graph i).IsClique (S j)) ∧
      ∀ u v, (Graph i).Adj u v → ∃ j, u ∈ S j ∧ v ∈ S j

open Classical in
/-- COVERING BY CLIQUES as a decision problem over bitstrings. -/
noncomputable def coveringByCliquesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoveringByCliquesInstance) x with
  | some i => decide (WellFormed i ∧ CoveringByCliquesFeasible i)
  | none => false

/-- **COVERING BY CLIQUES is NP-complete.** Source: Garey and Johnson (1979), [GT17];
Kou, Stockmeyer, and Wong (1978); Orlin (1977). -/
public theorem_wanted coveringByCliques_npComplete :
    coveringByCliquesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coveringByCliquesDec

end MetaMathlibExt.Complexity.NPComplete.CoveringByCliques
