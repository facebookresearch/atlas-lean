/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DENSEST k-SUBGRAPH is NP-complete

Source:
U. Feige, G. Kortsarz, and D. Peleg, "The dense k-subgraph problem" (2001); M. R. Garey and D.
S. Johnson, *Computers and Intractability* (1979), DENSEST k-SUBGRAPH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph

/-!
# DENSEST k-SUBGRAPH is NP-complete

An undirected graph, a vertex count `k`, and an edge threshold `m`. The question is whether
some set of exactly `k` vertices induces at least `m` edges, witnessed by a sublist of at least
`m` edges inside the set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A densest-k-subgraph instance: vertex count, edge list, vertex count k, edge threshold m. -/
abbrev DensestKSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : DensestKSubgraphInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1)

/-- `k` vertices inducing at least `m` edges. -/
def DensestKSubgraphFeasible
    (i : DensestKSubgraphInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧ S.card = i.2.2.1 ∧
    ∃ E' : List (ℕ × ℕ), E'.Sublist i.2.1 ∧ i.2.2.2 ≤ E'.length ∧
      ∀ e ∈ E', e.1 ∈ S ∧ e.2 ∈ S

open Classical in
/-- DENSEST k-SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def densestKSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DensestKSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ DensestKSubgraphFeasible i)
  | none => false

/-- **DENSEST k-SUBGRAPH is NP-complete.** Source: U. Feige, G. Kortsarz, and D. Peleg, "The
dense k-subgraph problem" (2001); M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), DENSEST k-SUBGRAPH. -/
public theorem_wanted densestKSubgraph_npComplete :
    densestKSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L densestKSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
