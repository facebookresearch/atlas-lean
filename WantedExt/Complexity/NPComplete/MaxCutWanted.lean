/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM CUT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM CUT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCut

/-!
# MAXIMUM CUT is NP-complete

An undirected graph and a bound `K`. The question is whether the vertices can be split into two
sets with at least `K` edges crossing between them, witnessed by a sublist of at least `K`
crossing edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list, bound. -/
abbrev MaxCutInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A cut with at least `K` edges. -/
def MaxCutFeasible
    (i : MaxCutInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧
    ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ i.2.2 ≤ cut.length ∧
      ∀ e ∈ cut, (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)

open Classical in
/-- MAXIMUM CUT as a decision problem over bitstrings. -/
noncomputable def maxCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **MAXIMUM CUT is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MAXIMUM CUT. -/
public theorem_wanted maxCut_npComplete :
    maxCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutDec

end MetaMathlibExt.Complexity.NPComplete.MaxCut
