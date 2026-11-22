/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH HOMOMORPHISM (identification of nonadjacent vertices) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT52] GRAPH HOMOMORPHISM;
L. A. Levin, "Universal sequential search problems", Problemy Peredachi Informatsii 9(3)
(1973), 115-116; English translation in Problems of Information Transmission 9 (1973),
265-266.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismIdentification

/-!
# GRAPH HOMOMORPHISM (identification of nonadjacent vertices) is NP-complete

Garey and Johnson's [GT52]. Given graphs `G = (V₁, E₁)` and `H = (V₂, E₂)`, can a graph
isomorphic to `H` be obtained from `G` by a sequence of identifications of nonadjacent
vertices, where each step replaces two nonadjacent vertices `u, v` by a single vertex `w`
adjacent to exactly those vertices that were previously adjacent to at least one of `u` and
`v`?

This is not the plain homomorphism problem of `GraphHomomorphismWanted` (is there any
homomorphism `G → H`): here every vertex and every edge of `H` must come from `G`.

A sequence of identifications merges the vertices of `G` into classes, each an independent set
of `G` (two vertices are identified only when no edge joins their classes), and the result is
the quotient graph: two classes are adjacent exactly when some edge of `G` joins them.
Conversely, a partition of `V₁` into independent sets is realized by identifying the members
of each class one at a time. A graph isomorphic to `H` is obtained exactly when there is a
surjective map `f : V₁ → V₂` whose fibers are independent sets of `G` and whose quotient
`G.map f` (Mathlib's image graph: `x ≠ y` are adjacent when some edge of `G` joins `f⁻¹ x`
and `f⁻¹ y`) is `H`. The empty sequence is allowed, so `H ≅ G` is a yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count and edge list of `G`, vertex count and edge list of `H`. -/
abbrev GraphHomomorphismIdentificationInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The graph `G` as a `SimpleGraph (Fin n₁)`. -/
def GraphG (i : GraphHomomorphismIdentificationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The graph `H` as a `SimpleGraph (Fin n₂)`. -/
def GraphH (i : GraphHomomorphismIdentificationInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: both edge lists are simple (in range, no loops, no
repeated edge in either orientation). -/
def WellFormed (i : GraphHomomorphismIdentificationInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧
      ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- `H` is obtained from `G` by identifying nonadjacent vertices: some surjective map
`f : V₁ → V₂` has fibers that are independent sets of `G`, and the quotient of `G` by its
fibers is `H`. -/
def GraphHomomorphismIdentificationFeasible (i : GraphHomomorphismIdentificationInstance) :
    Prop :=
  ∃ f : Fin i.1 → Fin i.2.2.1, Function.Surjective f ∧
    (∀ x, (GraphG i).IsIndepSet {v | f v = x}) ∧ (GraphG i).map f = GraphH i

open Classical in
/-- GRAPH HOMOMORPHISM ([GT52]) as a decision problem over bitstrings. -/
noncomputable def graphHomomorphismIdentificationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphHomomorphismIdentificationInstance) x with
  | some i => decide (WellFormed i ∧ GraphHomomorphismIdentificationFeasible i)
  | none => false

/-- **GRAPH HOMOMORPHISM (identification of nonadjacent vertices) is NP-complete.** Source:
Garey and Johnson (1979), [GT52]; Levin (1973). -/
public theorem_wanted graphHomomorphismIdentification_npComplete :
    graphHomomorphismIdentificationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphHomomorphismIdentificationDec

end MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismIdentification
