/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on circle graphs is NP-complete

Source:
J. M. Keil and L. Stewart, "Approximating the minimum clique cover and other hard problems in
subtree filament graphs", Discrete Applied Mathematics 154(14) (2006), 1983-1995,
doi:10.1016/j.dam.2006.03.003, Theorem 2.1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import WantedExt.Complexity.NPComplete.DominatingSetCircleGraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCircleGraph

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-!
# PARTITION INTO CLIQUES on circle graphs is NP-complete

INSTANCE: a circle graph `G = (V, E)`, given by a chord model (a family of chords of a circle,
one per vertex, two vertices adjacent when their chords intersect), and a positive integer
`K ≤ |V|`.
QUESTION: can `V` be partitioned into `k ≤ K` disjoint sets `V₁, …, V_k` such that each `Vᵢ`
induces a complete subgraph of `G`?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesWanted`) restricted to circle
graphs. Keil and Stewart (2006), Theorem 2.1, prove that the clique cover problem on circle
graphs, partitioning the vertex set into the minimum number of subsets each inducing a clique, is
NP-complete.

The chord model and the circle graph are those of
`WantedExt.Complexity.NPComplete.DominatingSetCircleGraphWanted`: a chord is given by its two
endpoints, natural numbers `a < b` naming points in clockwise order on the circle; the endpoints
of all chords are distinct; `DominatingSetCircleGraph.circleGraph` joins two chords when their
endpoints interleave (`a < c < b < d`, symmetrized by `SimpleGraph.fromRel`), which for distinct
endpoints is exactly when they intersect. Every circle graph has such a model (Keil and Stewart
work with the equivalent interval overlap model with distinct endpoints). The bound
`0 < K ≤ |V|` is the instance class of [GT15] (`PartitionIntoCliques.WellFormed`). The question
has the shape of `PartitionIntoCliques.PartitionIntoCliquesFeasible`: a block map `c : V → Fin k`
for some `k ≤ K` whose blocks are cliques (empty blocks are allowed and harmless).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the chords, one per vertex, each given by its endpoints `(a, b)`, and the bound
`K`. -/
abbrev PartitionIntoCliquesCircleGraphInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every chord has endpoints `a < b`, all endpoints of all
chords are distinct, and `0 < K ≤ |V|`. -/
def WellFormed (i : PartitionIntoCliquesCircleGraphInstance) : Prop :=
  (∀ c ∈ i.1, c.1 < c.2) ∧ (i.1.flatMap fun c => [c.1, c.2]).Nodup ∧ 0 < i.2 ∧ i.2 ≤ i.1.length

/-- The vertices of the circle graph split into at most `K` cliques: for some `k ≤ K` there is a
block map `c` whose blocks `c⁻¹(j)`, `j : Fin k`, are cliques of the circle graph. -/
def PartitionIntoCliquesCircleGraphFeasible (i : PartitionIntoCliquesCircleGraphInstance) :
    Prop :=
  ∃ k ≤ i.2, ∃ c : Fin i.1.length → Fin k, ∀ j : Fin k, (circleGraph i.1).IsClique {v | c v = j}

open Classical in
/-- PARTITION INTO CLIQUES on circle graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesCircleGraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesCircleGraphInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesCircleGraphFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES on circle graphs is NP-complete.** Source: Keil and Stewart (2006),
Theorem 2.1; Garey and Johnson (1979), [GT15]. -/
public theorem_wanted partitionIntoCliquesCircleGraph_npComplete :
    partitionIntoCliquesCircleGraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesCircleGraphDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCircleGraph
