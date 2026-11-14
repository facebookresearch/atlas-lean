/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO ISOMORPHIC SUBGRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT12] PARTITION INTO
ISOMORPHIC SUBGRAPHS;
D. G. Kirkpatrick and P. Hell, "On the completeness of a generalized matching
problem", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(1978), 240-245, doi:10.1145/800133.804353;
D. G. Kirkpatrick and P. Hell, "On the complexity of general graph factor
problems", SIAM Journal on Computing 12 (1983), 601-609, doi:10.1137/0212040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphs

/-!
# PARTITION INTO ISOMORPHIC SUBGRAPHS is NP-complete

INSTANCE: graphs `G = (V, E)` and `H = (V', E')` with `|V| = q|V'|` for some positive integer
`q`. QUESTION: can `V` be partitioned into `q` disjoint sets `V₁, ..., V_q` such that, for
each `i`, the subgraph of `G` induced by `Vᵢ` contains a spanning subgraph isomorphic to `H`
(a perfect `H`-packing, or `H`-factor, of `G`)?

This is the problem whose NP-completeness Kirkpatrick and Hell prove, for every fixed `H` with
a connected component of at least three vertices: the copies of `H` need not be induced.

The partition is a map `P : V → Fin q` with blocks `P⁻¹(k)`. "The subgraph induced by `P⁻¹(k)`
contains a spanning subgraph isomorphic to `H`" is a bijective graph homomorphism
`H →g G[P⁻¹(k)]`: the image of `H`'s edges is the spanning subgraph, and the homomorphism is
the isomorphism onto it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` of `G` (vertices `Fin n`), edge list of `G`, vertex count
`m` of `H` (vertices `Fin m`), edge list of `H`. -/
abbrev PartitionIntoIsomorphicSubgraphsInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoIsomorphicSubgraphsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The graph `H` of the instance as a `SimpleGraph (Fin m)`. -/
def Pattern (i : PartitionIntoIsomorphicSubgraphsInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: both edge lists describe simple graphs (no duplicate edges
in either orientation, no self-loops, endpoints in range), and `n = q * m` for some positive
integer `q`. -/
def WellFormed (i : PartitionIntoIsomorphicSubgraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2,
      e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2) ∧
    ∃ q, 0 < q ∧ i.1 = q * i.2.2.1

/-- The vertices of `G` split into blocks `P⁻¹(k)`, `k : Fin q`, such that each block's
induced subgraph contains a spanning copy of `H`: a bijective homomorphism from `H` onto the
block. -/
def PartitionIntoIsomorphicSubgraphsFeasible
    (i : PartitionIntoIsomorphicSubgraphsInstance) : Prop :=
  ∃ q, ∃ P : Fin i.1 → Fin q, ∀ k : Fin q,
    ∃ φ : Pattern i →g (Graph i).induce {v | P v = k}, Function.Bijective φ

open Classical in
/-- PARTITION INTO ISOMORPHIC SUBGRAPHS as a decision problem over bitstrings. -/
noncomputable def partitionIntoIsomorphicSubgraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoIsomorphicSubgraphsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoIsomorphicSubgraphsFeasible i)
  | none => false

/-- **PARTITION INTO ISOMORPHIC SUBGRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[GT12]; Kirkpatrick and Hell (1978, 1983). -/
public theorem_wanted partitionIntoIsomorphicSubgraphs_npComplete :
    partitionIntoIsomorphicSubgraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoIsomorphicSubgraphsDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphs
