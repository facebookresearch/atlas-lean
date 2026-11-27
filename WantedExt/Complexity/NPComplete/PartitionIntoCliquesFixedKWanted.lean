/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES is NP-complete for every fixed K ≥ 3

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES, comment:
remains NP-complete for all fixed `K ≥ 3`; solvable in polynomial time for `K ≤ 2`;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (CLIQUE COVER,
by transformation from GRAPH K-COLORABILITY);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1 (1976), 237-267, doi:10.1016/0304-3975(76)90059-1 (GRAPH
3-COLORABILITY).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesFixedK

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
  (PartitionIntoCliquesInstance PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES is NP-complete for every fixed K ≥ 3

Fix an integer `K ≥ 3`.
INSTANCE: a graph `G = (V, E)` (with `K ≤ |V|`). QUESTION: can the vertices of `G` be partitioned
into `k ≤ K` disjoint sets `V₁, V₂, …, V_k` such that, for `1 ≤ i ≤ k`, the subgraph induced by
`Vᵢ` is a complete graph?

Garey and Johnson [GT15] state PARTITION INTO CLIQUES with `K` in the instance and comment that it
remains NP-complete for all fixed `K ≥ 3`. A partition of `V` into `k` cliques of `G` is a
partition into `k` independent sets of the complement of `G`, so the problem for fixed `K` is
GRAPH K-COLORABILITY of the complement, which is NP-complete for every fixed `K ≥ 3` ([GT4],
comment).

`K` is fixed, not part of the input: the decision problem is `partitionIntoCliquesFixedKDec k`,
and the theorem holds for every `k ≥ 3`. The instance, the graph and the question are those of
`PartitionIntoCliquesWanted`, reused unchanged; the restriction adds to the parent's
well-formedness (simple edge list, `0 < K ≤ |V|`) that the bound in the instance is the fixed `k`,
as in `FixedKColorabilityWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed bound `k`: a well-formed PARTITION INTO CLIQUES
instance (simple edge list, `0 < K ≤ |V|`) whose bound is `k`. -/
def WellFormed (k : ℕ) (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ i.2.2 = k

open Classical in
/-- PARTITION INTO CLIQUES, for the fixed bound `k`, as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesFixedKDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed k i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES is NP-complete for every fixed `K ≥ 3`.** Source: Garey and Johnson
(1979), [GT15], comment; Karp (1972). -/
public theorem_wanted partitionIntoCliquesFixedK_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    partitionIntoCliquesFixedKDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (partitionIntoCliquesFixedKDec k)

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesFixedK
