/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ITERATED SHUFFLE MEMBERSHIP is NP-complete

Source:
M. K. Warmuth and D. Haussler, "On the complexity of iterated shuffle", Journal of Computer and
System Sciences 28 (1984), 345-358, doi:10.1016/0022-0000(84)90018-7 (as recorded by
M. Domaratzki, PhD thesis, Chapter 3, Theorem 3.2.1: "Let Σ = {a, b, c}. Given words
u, v ∈ Σ*, it is NP-complete to determine whether u ∈ (⧢)*(v)").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ShuffleOfSeveralStringsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IteratedShuffleMembership

open ShuffleOfSeveralStrings (shuffleAll)

/-!
# ITERATED SHUFFLE MEMBERSHIP is NP-complete

INSTANCE: strings `w` and `u` over a three-letter alphabet `Σ`.
QUESTION: is `w` in the iterated shuffle `u^⧢* = ⋃_{m ≥ 0} u ⧢ u ⧢ ⋯ ⧢ u` (`m` copies of `u`),
i.e. can `w` be obtained by interleaving the letters of some number of copies of `u`, keeping
the letters of each copy in order?

Warmuth and Haussler (1984) proved this NP-complete (by a reduction from 3-PARTITION), the
special case of SHUFFLE OF SEVERAL STRINGS (`ShuffleOfSeveralStringsWanted`) in which all the
shuffled strings are equal, already over the alphabet `{a, b, c}`. The number of copies is not
part of the input; it is `|w| / |u|` when `u` is nonempty. Membership in NP: a certificate
assigns each position of `w` to one of the at most `|w|` copies (for `u = ε` the iterated shuffle
is `{ε}`).

Letters are natural numbers and strings are lists of letters; the three-letter alphabet is
`{0, 1, 2}`, a conjunct of `WellFormed`. The shuffle of `m` copies of `u` is
`ShuffleOfSeveralStrings.shuffleAll (List.replicate m u)` (CSLibExt's `Cslib.Language.shuffle`,
right-nested, ending with `{ε}`; for `m = 0` it is `{ε}`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **ITERATED SHUFFLE MEMBERSHIP is NP-complete.** Source: Warmuth and Haussler (1984). -/
public theorem_wanted iteratedShuffleMembership_npComplete :
    iteratedShuffleMembershipDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L iteratedShuffleMembershipDec

end MetaMathlibExt.Complexity.NPComplete.IteratedShuffleMembership
