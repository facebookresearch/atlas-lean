/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR EXPRESSION SUBSTITUTION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR24] REGULAR EXPRESSION SUBSTITUTION
(attributed to A. V. Aho and J. D. Ullman [1977], private communication).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RegularExpressionInequivalenceBoundedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegularExpressionSubstitution

open MetaMathlibExt.Complexity.NPComplete.RegularExpressionInequivalenceBounded (parse ExprOver)

/-- An instance: the size `m` of `Y`, the postfix token list of `R`, the token lists of
`R₁, ..., Rₙ`, and the string `w`. -/
abbrev RegularExpressionSubstitutionInstance :=
  ℕ × List (ℕ × ℕ) × List (List (ℕ × ℕ)) × List ℕ

/-- Well-formedness of an instance: `R` is a regular expression over `X ∪ Y`
(letters below `m + n`), each `Rᵢ` is a regular expression over `Y` (letters below `m`), and
`w` is a string over `Y`. -/
def WellFormed (i : RegularExpressionSubstitutionInstance) : Prop :=
  (∃ R, ExprOver (i.1 + i.2.2.1.length) i.2.1 R) ∧
    (∀ toks ∈ i.2.2.1, ∃ E, ExprOver i.1 toks E) ∧ ∀ a ∈ i.2.2.2, a < i.1

/-- The result of substituting `ws[k]` (that is, `w_{k+1}`) for every occurrence of the symbol
`m + k` (that is, `x_{k+1}`) in `z`; symbols below `m` are kept. -/
def substitute (m : ℕ) (ws : List (List ℕ)) (z : List ℕ) : List ℕ :=
  z.flatMap fun a => if m ≤ a then ws.getD (a - m) [] else [a]

/-- Some `z ∈ L(R)` and strings `wᵢ ∈ L(Rᵢ)`, one for each `i`, make the substitution of `wᵢ`
for `xᵢ` in `z` equal to `w`. -/
def RegularExpressionSubstitutionFeasible (i : RegularExpressionSubstitutionInstance) : Prop :=
  ∃ R, parse i.2.1 = some R ∧ ∃ z ∈ R.matches', ∃ ws : List (List ℕ),
    List.Forall₂ (fun toks wᵢ => ∃ E, parse toks = some E ∧ wᵢ ∈ E.matches') i.2.2.1 ws ∧
      substitute i.1 ws z = i.2.2.2

open Classical in
/-- REGULAR EXPRESSION SUBSTITUTION as a decision problem over bitstrings. -/
noncomputable def regularExpressionSubstitutionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RegularExpressionSubstitutionInstance) x with
  | some i => decide (WellFormed i ∧ RegularExpressionSubstitutionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RegularExpressionSubstitution
