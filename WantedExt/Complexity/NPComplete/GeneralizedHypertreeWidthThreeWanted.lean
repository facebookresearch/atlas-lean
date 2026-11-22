/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED HYPERTREE WIDTH AT MOST 3 is NP-complete

Source:
G. Gottlob, Z. Miklós and T. Schwentick, "Generalized hypertree decompositions: NP-hardness and
tractable variants", Journal of the ACM 56 (2009), no. 6, 1-32, doi:10.1145/1568318.1568320;
W. Fischl, G. Gottlob and R. Pichler, "General and fractional hypertree decompositions: hard and
easy cases", Proceedings of the 37th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database
Systems (PODS 2018), 17-32, doi:10.1145/3196959.3196962 (arXiv:1611.01090), Section 1 (the
definition of generalized hypertree decompositions and width used below, and the attribution of
NP-completeness for `k = 3` to Gottlob, Miklós and Schwentick).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThree

/-!
# GENERALIZED HYPERTREE WIDTH AT MOST 3 is NP-complete

INSTANCE: a hypergraph `H = (V(H), E(H))`. QUESTION: is the generalized hypertree width of `H` at
most 3, i.e., is there a generalized hypertree decomposition `⟨T, (B_u), (λ_u)⟩` of `H` of width
at most 3? Such a decomposition consists of a tree `T`, a bag `B_u ⊆ V(H)` and a function
`λ_u : E(H) → {0, 1}` for every node `u` of `T`, such that
(1) for each `e ∈ E(H)` there is a node `u` with `e ⊆ B_u`;
(2) for each `v ∈ V(H)` the set `{u | v ∈ B_u}` is connected in `T`;
(3) for each node `u`, `B_u ⊆ B(λ_u)`, the set of vertices covered by the hyperedges `e` with
`λ_u(e) = 1`;
and its width is the maximum over the nodes `u` of the number of hyperedges with `λ_u(e) = 1`.

Vertices are `Fin n` and hyperedges are the list positions `Fin m` of a list of vertex lists.
The tree is Mathlib's `SimpleGraph.IsTree` on `Fin N` nodes for some `N`; the source's trees are
rooted, but conditions (1)-(3) do not mention the root. `λ_u` is given by the set of hyperedges
it maps to 1. Condition (2) is Mathlib's `Preconnected` for the subgraph of `T` induced on
`{u | v ∈ B_u}`, so that the empty set counts as connected: a vertex in no hyperedge lies in no
bag, by (3). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of vertices `n` (vertices `Fin n`) and the hyperedges, each a list of
vertices. -/
abbrev GeneralizedHypertreeWidthThreeInstance := ℕ × List (List ℕ)

/-- The vertex set of hyperedge `e`. -/
def edgeSet (i : GeneralizedHypertreeWidthThreeInstance) (e : Fin i.2.length) :
    Finset (Fin i.1) :=
  Finset.univ.filter fun v => v.1 ∈ i.2.get e

/-- Well-formedness of an instance: every hyperedge lists only vertices `< n`. -/
def WellFormed (i : GeneralizedHypertreeWidthThreeInstance) : Prop :=
  ∀ e ∈ i.2, ∀ v ∈ e, v < i.1

/-- `⟨T, B, Λ⟩` is a generalized hypertree decomposition of width at most 3: conditions (1)-(3),
and every `Λ u` (the hyperedges `e` with `λ_u(e) = 1`) has at most 3 elements. -/
def IsGHDWidthAtMostThree (i : GeneralizedHypertreeWidthThreeInstance) {N : ℕ}
    (T : SimpleGraph (Fin N)) (B : Fin N → Finset (Fin i.1)) (Λ : Fin N → Finset (Fin i.2.length)) :
    Prop :=
  T.IsTree ∧ (∀ e, ∃ u, edgeSet i e ⊆ B u) ∧
    (∀ v, (T.induce {u | v ∈ B u}).Preconnected) ∧
    (∀ u, B u ⊆ (Λ u).biUnion (edgeSet i)) ∧ ∀ u, (Λ u).card ≤ 3

/-- Some generalized hypertree decomposition of the hypergraph has width at most 3. -/
def GeneralizedHypertreeWidthThreeFeasible (i : GeneralizedHypertreeWidthThreeInstance) : Prop :=
  ∃ (N : ℕ) (T : SimpleGraph (Fin N)) (B : Fin N → Finset (Fin i.1))
    (Λ : Fin N → Finset (Fin i.2.length)), IsGHDWidthAtMostThree i T B Λ

open Classical in
/-- GENERALIZED HYPERTREE WIDTH AT MOST 3 as a decision problem over bitstrings. -/
noncomputable def generalizedHypertreeWidthThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedHypertreeWidthThreeInstance) x with
  | some i => decide (WellFormed i ∧ GeneralizedHypertreeWidthThreeFeasible i)
  | none => false

/-- **GENERALIZED HYPERTREE WIDTH AT MOST 3 is NP-complete.** Source: Gottlob, Miklós and
Schwentick (2009); Fischl, Gottlob and Pichler (2018), Section 1. -/
public theorem_wanted generalizedHypertreeWidthThree_npComplete :
    generalizedHypertreeWidthThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedHypertreeWidthThreeDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThree
