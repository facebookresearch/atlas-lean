/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHUFFLE OF SEVERAL STRINGS: definitions

Source:
M. K. Warmuth and D. Haussler, "On the complexity of iterated shuffle", Journal of Computer and
System Sciences 28 (1984), 345-358, doi:10.1016/0022-0000(84)90018-7;
A. Mansfield, "On the computational complexity of a merge recognition problem", Discrete
Applied Mathematics 5 (1983), 119-122, doi:10.1016/0166-218X(83)90021-5.
-/
module

public import CSLibExt.Computability.Languages.RegularShuffle
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShuffleOfSeveralStrings

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

end MetaMathlibExt.Complexity.NPComplete.ShuffleOfSeveralStrings
