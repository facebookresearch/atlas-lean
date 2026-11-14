/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLAR GRAPH RECOGNITION is NP-complete

Source:
Zh. A. Chernyak and A. A. Chernyak, "About recognizing (α, β) classes of polar graphs",
Discrete Mathematics 62 (1986), 133-138, doi:10.1016/0012-365X(86)90113-5;
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar
graphs", Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032;
ISGCI (https://www.graphclasses.org/classes/gc_314.html), problem "Recognition" on polar
graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ClusterDeletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarGraphRecognition

/-!
# POLAR GRAPH RECOGNITION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` polar, that is, can `V` be partitioned into sets `A` and `B` such that `A`
induces a complete multipartite graph and `B` induces a disjoint union of cliques?

Le and Nevries (2014), abstract: "A graph `G = (V, E)` is polar if its vertex set admits a
partition `V = A ∪ B` such that `A` induces a complete multipartite graph and `B` the complement
of a complete multipartite graph." The complement of a complete multipartite graph is a disjoint
union of cliques (ISGCI: "the connected components of `\overline{G[A]}` and of `G[B]` are
complete graphs"). Chernyak and Chernyak (1986) proved polar graph recognition NP-complete;
Le and Nevries prove it NP-complete already on small subclasses (for instance
`{2K₂, C₅}`-free co-planar graphs), which implies the general case. Membership in NP: the
partition is a certificate checked over all triples of vertices.

`IsPolar G` takes a set `A` and its complement `Aᶜ` (either may be empty). `A` induces (Mathlib's
`G.induce A`) a complete multipartite graph, Mathlib's `SimpleGraph.IsCompleteMultipartite`
(non-adjacency is transitive); `Aᶜ` induces a cluster graph (every connected component
complete), the predicate `ClusterDeletion.IsClusterGraph` of `ClusterDeletionWanted`, which the
merged monopolar statements also use for this part. The graph is given by an edge list on
`Fin n` as in the other graph statements of this directory (`Cslib.Complexity.Karp.edgeGraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev PolarGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PolarGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PolarGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` is polar: its vertex set splits into a set `A` inducing a complete multipartite graph
and the rest `Aᶜ` inducing a disjoint union of cliques. -/
def IsPolar {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A : Set (Fin n), (G.induce A).IsCompleteMultipartite ∧
    ClusterDeletion.IsClusterGraph (G.induce Aᶜ)

/-- The graph of the instance is polar. -/
def PolarGraphRecognitionFeasible (i : PolarGraphRecognitionInstance) : Prop :=
  IsPolar (Graph i)

open Classical in
/-- POLAR GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def polarGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ PolarGraphRecognitionFeasible i)
  | none => false

/-- **POLAR GRAPH RECOGNITION is NP-complete.** Source: Chernyak and Chernyak (1986); Le and
Nevries (2014). -/
public theorem_wanted polarGraphRecognition_npComplete :
    polarGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L polarGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.PolarGraphRecognition
