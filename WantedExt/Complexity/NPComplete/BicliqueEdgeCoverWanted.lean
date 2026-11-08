/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICLIQUE EDGE COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BICLIQUE COVER.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover

/-!
# BICLIQUE EDGE COVER is NP-complete

A bipartite graph (left vertices `0, …, L - 1`, right vertices `0, …, R - 1`) and a bound `K`.
The question is whether all edges can be covered by at most `K` complete bipartite subgraphs
(bicliques), each given by a left set and a right set with all cross pairs present as edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A biclique-edge-cover instance: left count, right count, edges, bound. -/
abbrev BicliqueEdgeCoverInstance := ℕ × ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : BicliqueEdgeCoverInstance) : Prop :=
  i.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2 < i.2.1

/-- At most `K` bicliques covering all edges. -/
def BicliqueEdgeCoverFeasible
    (i : BicliqueEdgeCoverInstance) : Prop :=
  ∃ bicliques : List (List ℕ × List ℕ), bicliques.length ≤ i.2.2.2 ∧
    (∀ p ∈ bicliques, (∀ a ∈ p.1, a < i.1) ∧ ∀ b ∈ p.2, b < i.2.1) ∧
    ∀ e ∈ i.2.2.1, ∃ p ∈ bicliques, e.1 ∈ p.1 ∧ e.2 ∈ p.2 ∧
      ∀ a ∈ p.1, ∀ b ∈ p.2, (a, b) ∈ i.2.2.1

open Classical in
/-- BICLIQUE EDGE COVER as a decision problem over bitstrings. -/
noncomputable def bicliqueEdgeCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BicliqueEdgeCoverInstance) x with
  | some i => decide (WellFormed i ∧ BicliqueEdgeCoverFeasible i)
  | none => false

/-- **BICLIQUE EDGE COVER is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), BICLIQUE COVER. -/
public theorem_wanted bicliqueEdgeCover_npComplete :
    bicliqueEdgeCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bicliqueEdgeCoverDec

end MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover
