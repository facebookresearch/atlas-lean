/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBGRAPH ISOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SUBGRAPH ISOMORPHISM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism

/-!
# SUBGRAPH ISOMORPHISM is NP-complete

Two undirected graphs, pattern `H` and host `G`. The question is whether `H` is a (not
necessarily induced) subgraph of `G`: an injective map from the vertices of `H` to those of `G`
sending every edge of `H` to an edge of `G`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A subgraph-isomorphism instance: host vertex count, host edges, pattern vertex count,
pattern edges. -/
abbrev SubgraphIsomorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)


/-- The host graph. -/
def GraphHost (i : SubgraphIsomorphismInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- Well-formedness of an instance. -/
def WellFormed (i : SubgraphIsomorphismInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- An injective edge-preserving map from the pattern to the host. -/
def SubgraphIsomorphismFeasible
    (i : SubgraphIsomorphismInstance) : Prop :=
  ∃ f : Fin i.2.2.1 → Fin i.1, Function.Injective f ∧
    ∀ e ∈ i.2.2.2, ∀ (h1 : e.1 < i.2.2.1) (h2 : e.2 < i.2.2.1),
      (GraphHost i).Adj (f ⟨e.1, h1⟩) (f ⟨e.2, h2⟩)

open Classical in
/-- SUBGRAPH ISOMORPHISM as a decision problem over bitstrings. -/
noncomputable def subgraphIsomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphIsomorphismFeasible i)
  | none => false

/-- **SUBGRAPH ISOMORPHISM is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), SUBGRAPH ISOMORPHISM. -/
public theorem_wanted subgraphIsomorphism_npComplete :
    subgraphIsomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L subgraphIsomorphismDec

end MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism
