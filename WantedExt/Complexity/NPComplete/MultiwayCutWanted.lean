/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIWAY CUT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MULTIWAY CUT; E. Dahlhaus
et al., "The complexity of multiterminal cuts" (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayCut

/-!
# MULTIWAY CUT is NP-complete

An undirected graph, a list of terminals, and a bound `K`. The question is whether the
terminals can be pairwise separated by removing at most `K` edges, witnessed by an assignment
of every vertex to one terminal's part, sending each terminal to its own part, with at most `K`
cut edges, stated by forbidding `K + 1` cut edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A multiway-cut instance: vertex count, edge list, terminals, bound. -/
abbrev MultiwayCutInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MultiwayCutInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.Nodup ∧ ∀ t ∈ i.2.2.1, t < i.1

/-- A separation of all terminals with at most `K` cut edges. -/
def MultiwayCutFeasible
    (i : MultiwayCutInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1 ∧
    (∀ v < i.1, assign.getD v 0 < max i.2.2.1.length 1) ∧
    (∀ t < i.2.2.1.length, assign.getD (i.2.2.1.getD t 0) 0 = t) ∧
    ¬ ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ cut.length = i.2.2.2 + 1 ∧
      ∀ e ∈ cut, assign.getD e.1 0 ≠ assign.getD e.2 0

open Classical in
/-- MULTIWAY CUT as a decision problem over bitstrings. -/
noncomputable def multiwayCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiwayCutInstance) x with
  | some i => decide (WellFormed i ∧ MultiwayCutFeasible i)
  | none => false

/-- **MULTIWAY CUT is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MULTIWAY CUT; E. Dahlhaus et al., "The complexity of multiterminal
cuts" (1994). -/
public theorem_wanted multiwayCut_npComplete :
    multiwayCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiwayCutDec

end MetaMathlibExt.Complexity.NPComplete.MultiwayCut
