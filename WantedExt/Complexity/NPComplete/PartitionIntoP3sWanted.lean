/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PATHS OF LENGTH 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION INTO PATHS; M.
E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected subgraphs",
Discrete Applied Mathematics 10 (1985), 139-153.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoP3s

/-!
# PARTITION INTO PATHS OF LENGTH 2 is NP-complete

An undirected graph. The question is whether the vertices can be partitioned into triples, each
containing a path on three vertices: two consecutive edges of the triple. The path need not be
induced: a triangle triple qualifies, using two of its three edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of PARTITION INTO PATHS OF LENGTH 2.** An instance of PARTITION INTO PATHS OF
LENGTH 2 is a pair $(n, E)$ of a natural number $n$, the number of vertices, and a finite list
$E$ of pairs of natural numbers, the edge list. -/
abbrev PartitionIntoP3sInstance := ℕ × List (ℕ × ℕ)

/-- **Graph of a PARTITION INTO PATHS OF LENGTH 2 instance.** For an instance $(n, E)$, the graph
of the instance is the simple graph on the vertex set $\{0, \dots, n - 1\}$ in which distinct
vertices $u$ and $v$ are adjacent exactly when $(u, v)$ or $(v, u)$ belongs to $E$. Pairs in $E$
with an entry at least $n$, and pairs $(u, u)$, contribute no edge. -/
def Graph (i : PartitionIntoP3sInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- **Well-formed PARTITION INTO PATHS OF LENGTH 2 instances.** An instance $(n, E)$ is well
formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$ and $u \ne v$, and the reversed pair $(v, u)$ does not belong to $E$. -/
def WellFormed (i : PartitionIntoP3sInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- **Partitions into paths of length 2.** An instance $(n, E)$ admits a partition into paths of
length 2 when there is a list of triples, each a list of three distinct vertices from
$\{0, \dots, n - 1\}$, such that every vertex occurs exactly once among all the triples taken
together, and every triple contains pairwise distinct vertices $x$, $y$, $z$ such that $x$ is
adjacent to $y$ and $y$ is adjacent to $z$ in the graph of the instance.

The path need not be induced: a triple spanning a triangle qualifies. -/
def PartitionIntoP3sFeasible
    (i : PartitionIntoP3sInstance) : Prop :=
  ∃ triples : List (List (Fin i.1)), triples.flatten.Perm (List.finRange i.1) ∧
    (∀ t ∈ triples, t.length = 3 ∧ t.Nodup) ∧
    ∀ t ∈ triples, ∃ x ∈ t, ∃ y ∈ t, ∃ z ∈ t,
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ (Graph i).Adj x y ∧ (Graph i).Adj y z

open Classical in
/-- **PARTITION INTO PATHS OF LENGTH 2.** The decision problem PARTITION INTO PATHS OF LENGTH 2
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of
instances, to an instance $(n, E)$ that is well formed and admits a partition into paths of
length 2. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def partitionIntoP3sDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoP3sInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoP3sFeasible i)
  | none => false

/-- **PARTITION INTO PATHS OF LENGTH 2 is NP-complete.** The decision problem PARTITION INTO PATHS
OF LENGTH 2 belongs to NP, and every decision problem in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), PARTITION INTO PATHS; M. E. Dyer and A. M.
Frieze, "On the complexity of partitioning graphs into connected subgraphs", Discrete
Applied Mathematics 10 (1985), 139-153. -/
public theorem_wanted partitionIntoP3s_npComplete :
    partitionIntoP3sDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoP3sDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoP3s
