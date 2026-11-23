/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HITTING STRING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR12] HITTING STRING (reference: [Fagin, 1974];
transformation from 3SAT);
R. Fagin, "Generalized first-order spectra and polynomial-time recognizable sets", in
*Complexity of Computation* (R. M. Karp, ed.), SIAM-AMS Proceedings 7 (1974), 43-73, Section 10,
Theorem 36.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HittingString

/-!
# HITTING STRING is NP-complete

INSTANCE: a finite set `A` of strings over `{0, 1, *}`, all having the same length `n`.
QUESTION: is there a string `x ∈ {0, 1}*` with `|x| = n` such that for each string `a ∈ A`
there is some `i`, `1 ≤ i ≤ n`, for which the `i`-th symbol of `a` and the `i`-th symbol of `x`
are identical?

A string of `A` is a list of numbers, `0` and `1` for the symbols `0` and `1` and `2` for `*`;
the string `x` is a list of `n` truth values, `false` for `0` and `true` for `1`, so its `i`-th
symbol is `Bool.toNat` of its `i`-th entry. Positions are indexed from `0`. The symbol `*` is
identical to no symbol of `x`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the common length `n` and the strings of `A` (`0`, `1`, and `2` for `*`). -/
abbrev HittingStringInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance: every string of `A` has length `n` and its symbols are `0`,
`1` or `2` (for `*`). -/
def WellFormed (i : HittingStringInstance) : Prop :=
  ∀ a ∈ i.2, a.length = i.1 ∧ ∀ c ∈ a, c ≤ 2

/-- A string `x ∈ {0, 1}ⁿ` that agrees with every string of `A` in some position. -/
def HittingStringFeasible (i : HittingStringInstance) : Prop :=
  ∃ x : List Bool, x.length = i.1 ∧
    ∀ a ∈ i.2, ∃ k < i.1, a.getD k 2 = (x.getD k false).toNat

open Classical in
/-- HITTING STRING as a decision problem over bitstrings. -/
noncomputable def hittingStringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HittingStringInstance) x with
  | some i => decide (WellFormed i ∧ HittingStringFeasible i)
  | none => false

/-- **HITTING STRING is NP-complete.** Source: Garey and Johnson (1979), [SR12]; Fagin (1974),
Theorem 36. -/
public theorem_wanted hittingString_npComplete :
    hittingStringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hittingStringDec

end MetaMathlibExt.Complexity.NPComplete.HittingString
