/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM LINEAR ARRANGEMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM LINEAR
ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumLinearArrangement

/-!
# MINIMUM LINEAR ARRANGEMENT is NP-complete

An undirected graph and a bound `K`. The question is whether the vertices can be labeled with
`0, …, n - 1` (a bijection) so that the sum over edges of the label differences is at most `K`.

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
abbrev MinimumLinearArrangementInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MinimumLinearArrangementInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A labeling of total edge length at most `K`. -/
def MinimumLinearArrangementFeasible
    (i : MinimumLinearArrangementInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    (i.2.1.map (fun e => Nat.dist (perm.idxOf e.1) (perm.idxOf e.2))).sum ≤ i.2.2

open Classical in
/-- MINIMUM LINEAR ARRANGEMENT as a decision problem over bitstrings. -/
noncomputable def minimumLinearArrangementDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumLinearArrangementFeasible i)
  | none => false

/-- **MINIMUM LINEAR ARRANGEMENT is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MINIMUM LINEAR ARRANGEMENT. -/
public theorem_wanted minimumLinearArrangement_npComplete :
    minimumLinearArrangementDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumLinearArrangementDec

end MetaMathlibExt.Complexity.NPComplete.MinimumLinearArrangement
