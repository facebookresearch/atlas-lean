/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREFIX REVERSAL DISTANCE FOR BINARY STRINGS is NP-complete

Source:
C. Hurkens, L. van Iersel, J. Keijsper, S. Kelk, L. Stougie and J. Tromp, "Prefix reversals on
binary and ternary strings", SIAM Journal on Discrete Mathematics 21(3) (2007), 592-611,
doi:10.1137/060664252, Theorem 9 (the decision problem binary-PD is NP-complete, by a reduction
from 3-PARTITION); preprint arXiv:math/0602456.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PancakeFlippingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PancakeFlippingBinaryStrings

/-!
# PREFIX REVERSAL DISTANCE FOR BINARY STRINGS is NP-complete

INSTANCE (binary-PD in Hurkens et al.): two compatible fully binary strings `s` and `t` of
length `n`, and a bound `B ∈ ℤ⁺`. A string is fully binary if it is a string over `{0, 1}` in
which both symbols occur; two strings are compatible if they have the same symbol frequencies
(and hence the same length).
QUESTION: is the prefix reversal (flip) distance `d(s, t)` at most `B`, that is, can `s` be
transformed into `t` by at most `B` prefix reversals?

The prefix reversal `f⁽ʳ⁾` reverses the first `r` symbols of a string of length at least `r`;
it is `PancakeFlipping.flip r`, the flip of SORTING BY PREFIX REVERSALS. A sequence of flips is
applied from the first to the last. Compatibility is `List.Perm` (equal symbol multisets); since
`t` is a permutation of `s`, `t` is fully binary as soon as `s` is.

Membership in NP: compatible strings `s, t` of length `n` have `d(s, t) ≤ 2n` (Hurkens et al.,
footnote to Theorem 9), so a shortest flip sequence is a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the strings `s` and `t` (lists of symbols) and the bound `B`. -/
abbrev PancakeFlippingBinaryStringsInstance := List ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: `s` is a fully binary string (every symbol is `0` or `1`,
and both occur), `t` is compatible with `s` (a permutation of it), and `B` is positive. -/
def WellFormed (i : PancakeFlippingBinaryStringsInstance) : Prop :=
  (∀ a ∈ i.1, a < 2) ∧ 0 ∈ i.1 ∧ 1 ∈ i.1 ∧ i.1.Perm i.2.1 ∧ 0 < i.2.2

/-- Some sequence of at most `B` flips, each of a length `r` with `1 ≤ r ≤ n`, applied in order,
turns `s` into `t`. -/
def PancakeFlippingBinaryStringsFeasible (i : PancakeFlippingBinaryStringsInstance) : Prop :=
  ∃ rs : List ℕ, rs.length ≤ i.2.2 ∧ (∀ r ∈ rs, 1 ≤ r ∧ r ≤ i.1.length) ∧
    rs.foldl (fun x r => PancakeFlipping.flip r x) i.1 = i.2.1

open Classical in
/-- PREFIX REVERSAL DISTANCE FOR BINARY STRINGS as a decision problem over bitstrings. -/
noncomputable def pancakeFlippingBinaryStringsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PancakeFlippingBinaryStringsInstance) x with
  | some i => decide (WellFormed i ∧ PancakeFlippingBinaryStringsFeasible i)
  | none => false

/-- **PREFIX REVERSAL DISTANCE FOR BINARY STRINGS is NP-complete.** Source: Hurkens, van Iersel,
Keijsper, Kelk, Stougie and Tromp (2007), Theorem 9. -/
public theorem_wanted pancakeFlippingBinaryStrings_npComplete :
    pancakeFlippingBinaryStringsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pancakeFlippingBinaryStringsDec

end MetaMathlibExt.Complexity.NPComplete.PancakeFlippingBinaryStrings
