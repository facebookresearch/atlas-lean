/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on monopolar graphs is NP-complete

Source:
M. Barbato and D. Bezzi, "Monopolar graphs: Complexity of computing classical graph
parameters", Discrete Applied Mathematics 291 (2021), 277-285, doi:10.1016/j.dam.2020.12.023;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES;
ISGCI (https://www.graphclasses.org/classes/gc_1272.html), problem "Clique cover" on monopolar
graphs: NP-complete, with the attribution to Barbato and Bezzi.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesMonopolarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMonopolar

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph WellFormed
  PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES on monopolar graphs is NP-complete

INSTANCE: a monopolar graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: can the
vertices of `G` be partitioned into `k ≤ K` sets each of which induces a complete graph?

A graph is monopolar (Barbato and Bezzi, Section 1; ISGCI class `gc_1272`) if its vertex set can
be partitioned into a stable set `A` and a set `B` inducing a disjoint union of complete graphs,
i.e. every connected component of `G[B]` is complete. "Complete components" is the cluster-graph
predicate `ClusterDeletion.IsClusterGraph` (two distinct vertices joined by a walk are adjacent),
applied to the induced subgraph `G.induce Aᶜ`; stability of `A` is Mathlib's `IsIndepSet`.

The instance, its graph, its well-formedness (a simple edge list and `0 < K ≤ |V|`) and the
question are those of PARTITION INTO CLIQUES (`PartitionIntoCliquesDefs`, Garey and Johnson's
[GT15]); this module adds the monopolar restriction to well-formedness. Barbato and Bezzi prove
that computing the clique partitioning number of a monopolar graph is NP-hard, by reductions whose
graphs come with their monopolar partition. Recognizing monopolar graphs is itself NP-complete, but
the partition `(A, B)` together with a clique partition is a polynomial certificate, so the
restricted problem is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO CLIQUES on monopolar graphs is NP-complete.** Source: Barbato and Bezzi
(2021); Garey and Johnson (1979), [GT15]; ISGCI, class `gc_1272`. -/
public theorem_wanted partitionIntoCliquesMonopolar_npComplete :
    partitionIntoCliquesMonopolarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesMonopolarDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMonopolar
