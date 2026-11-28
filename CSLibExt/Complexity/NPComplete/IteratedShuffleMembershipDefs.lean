/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ITERATED SHUFFLE MEMBERSHIP: definitions

Source:
M. K. Warmuth and D. Haussler, "On the complexity of iterated shuffle", Journal of Computer and
System Sciences 28 (1984), 345-358, doi:10.1016/0022-0000(84)90018-7 (as recorded by
M. Domaratzki, PhD thesis, Chapter 3, Theorem 3.2.1: "Let Σ = {a, b, c}. Given words
u, v ∈ Σ*, it is NP-complete to determine whether u ∈ (⧢)*(v)").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ShuffleOfSeveralStringsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IteratedShuffleMembership

open ShuffleOfSeveralStrings (shuffleAll)

/-- An instance: the string `w` and the string `u`. -/
abbrev IteratedShuffleMembershipInstance := List ℕ × List ℕ

/-- Well-formedness of an instance: both strings are over the alphabet `{0, 1, 2}`. -/
def WellFormed (i : IteratedShuffleMembershipInstance) : Prop :=
  (∀ a ∈ i.1, a < 3) ∧ ∀ a ∈ i.2, a < 3

/-- `w` is in the iterated shuffle of `u`: it is a shuffle of `m` copies of `u` for some `m`. -/
def IteratedShuffleMembershipFeasible (i : IteratedShuffleMembershipInstance) : Prop :=
  ∃ m : ℕ, i.1 ∈ shuffleAll (List.replicate m i.2)

open Classical in
/-- ITERATED SHUFFLE MEMBERSHIP as a decision problem over bitstrings. -/
noncomputable def iteratedShuffleMembershipDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IteratedShuffleMembershipInstance) x with
  | some i => decide (WellFormed i ∧ IteratedShuffleMembershipFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IteratedShuffleMembership
