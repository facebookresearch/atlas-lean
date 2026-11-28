/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUASI-REAL-TIME LANGUAGE MEMBERSHIP for two grammars: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL18] QUASI-REAL-TIME LANGUAGE
MEMBERSHIP, comment ("remains NP-complete if `L₃ = Σ*`");
S. A. Greibach, "Jump PDA's, deterministic context-free languages, principal AFDLs and
polynomial time recognition (extended abstract)", Proc. 5th Annual ACM Symposium on Theory
of Computing (1973), 20-28, doi:10.1145/800125.804031.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembershipDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembershipTwoGrammars

open MetaMathlibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembership
  (GrammarData toEncodedCFG GrammarWellFormed)

/-- An instance: the number `k` of terminals (`Σ = {0, ..., k - 1}`), the grammars `G₁` and
`G₂` over `Σ`, the size `m` of the second alphabet (`Γ = {0, ..., m - 1}`), the function
`h : Σ → Γ` as the list `[h 0, ..., h (k - 1)]`, and the string `w`. -/
abbrev QuasiRealTimeLanguageMembershipTwoGrammarsInstance :=
  ℕ × GrammarData × GrammarData × ℕ × List ℕ × List ℕ

/-- Well-formedness of an instance: both grammars are well-formed over
`Σ = {0, ..., k - 1}`, `h` has one value for each letter of `Σ`, and the values of `h` and
the letters of `w` lie in `Γ = {0, ..., m - 1}`. -/
def WellFormed : QuasiRealTimeLanguageMembershipTwoGrammarsInstance → Prop
  | (k, g₁, g₂, m, h, w) =>
    GrammarWellFormed k g₁ ∧ GrammarWellFormed k g₂ ∧
      h.length = k ∧ (∀ c ∈ h, c < m) ∧ ∀ c ∈ w, c < m

/-- `w` is the letter-by-letter image under `h` of a word over `Σ` that both grammars
generate. -/
def QuasiRealTimeLanguageMembershipTwoGrammarsFeasible :
    QuasiRealTimeLanguageMembershipTwoGrammarsInstance → Prop
  | (k, g₁, g₂, _, h, w) =>
    ∃ x : List ℕ, (∀ a ∈ x, a < k) ∧
      x ∈ (toEncodedCFG g₁).language ∧ x ∈ (toEncodedCFG g₂).language ∧
      x.map (fun a => h.getD a 0) = w

open Classical in
/-- QUASI-REAL-TIME LANGUAGE MEMBERSHIP for two grammars as a decision problem over
bitstrings. -/
noncomputable def quasiRealTimeLanguageMembershipTwoGrammarsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuasiRealTimeLanguageMembershipTwoGrammarsInstance) x with
  | some i => decide (WellFormed i ∧ QuasiRealTimeLanguageMembershipTwoGrammarsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembershipTwoGrammars
