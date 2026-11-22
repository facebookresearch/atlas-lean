/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM k-CUT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM k-CUT (the `k =
2` slice is MAX CUT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxKCut

/-!
# MAXIMUM k-CUT is NP-complete

An undirected graph, a number `k` of parts, and a bound `K`. The question is whether the
vertices can be split into `k` parts with at least `K` edges crossing between parts, witnessed
by a sublist of at least `K` crossing edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A MAX-k-CUT instance: vertex count, edge list, number of parts k, bound. -/
abbrev MaxKCutInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MaxKCutInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1)

/-- A `k`-cut with at least `K` edges. -/
def MaxKCutFeasible
    (i : MaxKCutInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1 ∧ (∀ v < i.1, assign.getD v 0 < i.2.2.1) ∧
    ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ i.2.2.2 ≤ cut.length ∧
      ∀ e ∈ cut, assign.getD e.1 0 ≠ assign.getD e.2 0

open Classical in
/-- MAXIMUM k-CUT as a decision problem over bitstrings. -/
noncomputable def maxKCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxKCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxKCutFeasible i)
  | none => false

/-- **MAXIMUM k-CUT is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MAXIMUM k-CUT (the `k = 2` slice is MAX CUT). -/
public theorem_wanted maxKCut_npComplete :
    maxKCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxKCutDec

end MetaMathlibExt.Complexity.NPComplete.MaxKCut
