/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO TRIANGLES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION INTO TRIANGLES;
D. G. Kirkpatrick and P. Hell, "On the complexity of general graph factor problems", SIAM
Journal on Computing 12 (1983), 601-609.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoTriangles

/-!
# PARTITION INTO TRIANGLES is NP-complete

An undirected graph. The question is whether the vertices can be partitioned into triples, each
inducing a triangle (all three pairs adjacent).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of PARTITION INTO TRIANGLES.** An instance of PARTITION INTO TRIANGLES is a pair
consisting of a natural number $n$, the number of vertices, and a list of pairs of natural
numbers, the edges. -/
abbrev PartitionIntoTrianglesInstance := ℕ × List (ℕ × ℕ)

/-- **Graph of a PARTITION INTO TRIANGLES instance.** For an instance consisting of a natural number
$n$ and a list $E$ of pairs of natural numbers, its graph is the graph of the edge list $E$ on $n$
vertices: the simple graph on $\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are
adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. Pairs with an endpoint at least $n$ contribute
no edge. -/
def Graph (i : PartitionIntoTrianglesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- **Well-formed PARTITION INTO TRIANGLES instances.** An instance consisting of a natural number
$n$ and a list $E$ of pairs of natural numbers is well formed when $E$ has no repeated entries
and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$. -/
def WellFormed (i : PartitionIntoTrianglesInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- **Partition into triangles.** An instance consisting of a natural number $n$ and a list $E$ of
pairs of natural numbers admits a partition into triangles when the vertex set
$\{0, \dots, n - 1\}$ can be partitioned into sets of three vertices, any two of which are
adjacent in the graph of $E$ on $n$ vertices. -/
def PartitionIntoTrianglesFeasible
    (i : PartitionIntoTrianglesInstance) : Prop :=
  ∃ triples : List (List (Fin i.1)), triples.flatten.Perm (List.finRange i.1) ∧
    (∀ t ∈ triples, t.length = 3 ∧ t.Nodup) ∧
    ∀ t ∈ triples, ∀ a ∈ t, ∀ b ∈ t, a ≠ b → (Graph i).Adj a b

open Classical in
/-- **PARTITION INTO TRIANGLES as a decision problem.** The decision problem PARTITION INTO
TRIANGLES accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an instance consisting of a natural number $n$ and a list $E$ of pairs of natural
numbers such that $E$ has no repeated entries, every pair $(u, v)$ in $E$ satisfies $u < n$,
$v < n$, $u \ne v$ and $(v, u) \notin E$, and the vertex set $\{0, \dots, n - 1\}$ can be
partitioned into sets of three vertices, any two of which are adjacent in the graph of $E$ on $n$
vertices. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def partitionIntoTrianglesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoTrianglesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoTrianglesFeasible i)
  | none => false

/-- **PARTITION INTO TRIANGLES is NP-complete.** The decision problem PARTITION INTO TRIANGLES
lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to
PARTITION INTO TRIANGLES.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), PARTITION INTO TRIANGLES; D. G. Kirkpatrick and P.
Hell, "On the complexity of general graph factor problems", SIAM Journal on Computing 12
(1983), 601-609. -/
public theorem_wanted partitionIntoTriangles_npComplete :
    partitionIntoTrianglesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoTrianglesDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoTriangles
