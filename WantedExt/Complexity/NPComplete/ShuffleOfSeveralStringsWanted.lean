/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHUFFLE OF SEVERAL STRINGS is NP-complete

Source:
M. K. Warmuth and D. Haussler, "On the complexity of iterated shuffle", Journal of Computer and
System Sciences 28 (1984), 345-358, doi:10.1016/0022-0000(84)90018-7;
A. Mansfield, "On the computational complexity of a merge recognition problem", Discrete
Applied Mathematics 5 (1983), 119-122, doi:10.1016/0166-218X(83)90021-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Languages.RegularShuffle
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShuffleOfSeveralStrings

/-!
# SHUFFLE OF SEVERAL STRINGS is NP-complete

INSTANCE: strings `u₁, …, u_k` and `w` over a finite alphabet `Σ`.
QUESTION: is `w` in the shuffle `u₁ ⧢ u₂ ⧢ ⋯ ⧢ u_k`, i.e., can `w` be obtained by interleaving
the letters of `u₁, …, u_k`, keeping the letters of each `uᵢ` in their order?

The number `k` of strings is part of the input; for every fixed `k` the problem is solvable in
polynomial time (Mansfield 1983).

Letters are natural numbers and strings are lists of letters. The shuffle of two languages is
CSLibExt's `Cslib.Language.shuffle` (built on `Cslib.Language.IsShuffle`), and
`u₁ ⧢ ⋯ ⧢ u_k` is the right-nested shuffle `{u₁} ⧢ ({u₂} ⧢ ⋯ ({u_k} ⧢ {ε}))`; for `k = 0` it
is `{ε}`. The strings `u₁, …, u_k` are given as a list, and a repeated entry is a repeated
string of the shuffle.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the strings `u₁, …, u_k` and the string `w`. -/
abbrev ShuffleOfSeveralStringsInstance := List (List ℕ) × List ℕ

/-- The shuffle `u₁ ⧢ u₂ ⧢ ⋯ ⧢ u_k` of the strings of the list, as a language: the
right-nested shuffle of the singleton languages `{uᵢ}`, ending with `{ε}`. -/
def shuffleAll (us : List (List ℕ)) : Language ℕ :=
  us.foldr (fun u L => Cslib.Language.shuffle {u} L) 1

/-- `w` is in the shuffle of `u₁, …, u_k`. -/
def ShuffleOfSeveralStringsFeasible (i : ShuffleOfSeveralStringsInstance) : Prop :=
  i.2 ∈ shuffleAll i.1

open Classical in
/-- SHUFFLE OF SEVERAL STRINGS as a decision problem over bitstrings. -/
noncomputable def shuffleOfSeveralStringsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShuffleOfSeveralStringsInstance) x with
  | some i => decide (ShuffleOfSeveralStringsFeasible i)
  | none => false

/-- **SHUFFLE OF SEVERAL STRINGS is NP-complete.** Source: Warmuth and Haussler (1984);
Mansfield (1983). -/
public theorem_wanted shuffleOfSeveralStrings_npComplete :
    shuffleOfSeveralStringsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shuffleOfSeveralStringsDec

end MetaMathlibExt.Complexity.NPComplete.ShuffleOfSeveralStrings
