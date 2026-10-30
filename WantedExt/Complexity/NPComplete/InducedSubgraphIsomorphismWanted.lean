/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED SUBGRAPH ISOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), INDUCED SUBGRAPH
ISOMORPHISM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedSubgraphIsomorphism

/-!
# INDUCED SUBGRAPH ISOMORPHISM is NP-complete

Two undirected graphs, pattern `H` and host `G`. The question is whether `H` is an induced
subgraph of `G`: an injective map from the vertices of `H` to those of `G` preserving adjacency
in both directions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An induced-subgraph-isomorphism instance: host vertex count, host edges, pattern vertex
count, pattern edges. -/
abbrev InducedSubgraphIsomorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)


/-- The host graph. -/
def GraphHost (i : InducedSubgraphIsomorphismInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The pattern graph. -/
def GraphPattern (i : InducedSubgraphIsomorphismInstance) :
    SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2


/-- Well-formedness of an instance. -/
def WellFormed (i : InducedSubgraphIsomorphismInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- An injective adjacency-preserving map from the pattern to the host. -/
def InducedSubgraphIsomorphismFeasible
    (i : InducedSubgraphIsomorphismInstance) : Prop :=
  ∃ f : Fin i.2.2.1 → Fin i.1, Function.Injective f ∧
    ∀ a b : Fin i.2.2.1,
      (GraphPattern i).Adj a b ↔ (GraphHost i).Adj (f a) (f b)

open Classical in
/-- INDUCED SUBGRAPH ISOMORPHISM as a decision problem over bitstrings. -/
noncomputable def inducedSubgraphIsomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedSubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ InducedSubgraphIsomorphismFeasible i)
  | none => false

/-- **INDUCED SUBGRAPH ISOMORPHISM is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), INDUCED SUBGRAPH ISOMORPHISM. -/
public theorem_wanted inducedSubgraphIsomorphism_npComplete :
    inducedSubgraphIsomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedSubgraphIsomorphismDec

end MetaMathlibExt.Complexity.NPComplete.InducedSubgraphIsomorphism
