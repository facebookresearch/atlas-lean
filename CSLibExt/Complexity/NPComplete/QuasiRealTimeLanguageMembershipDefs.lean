/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUASI-REAL-TIME LANGUAGE MEMBERSHIP: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL18] QUASI-REAL-TIME LANGUAGE
MEMBERSHIP;
H. B. Hunt III, "On the time and tape complexity of languages I", Proc. 5th Annual ACM
Symposium on Theory of Computing (1973), 10-19, doi:10.1145/800125.804030;
S. A. Greibach, "The hardest context-free language", SIAM Journal on Computing 2 (1973),
304-310, doi:10.1137/0202025.
-/
module

public import CSLibExt.Computability.Languages.ContextFree.Encoded
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembership

/-- A context-free grammar as data: the number `n` of nonterminals (they are
`0, ..., n - 1`), the initial nonterminal, and the productions. A production `(A, w)` has
left-hand side `A` and right-hand side `w`, in which `(false, B)` is nonterminal `B` and
`(true, a)` is terminal `a`. -/
abbrev GrammarData := ℕ × ℕ × List (ℕ × List (Bool × ℕ))

/-- An instance: the number `k` of terminals (`Σ = {0, ..., k - 1}`), the grammars `G₁`,
`G₂`, `G₃` over `Σ`, the size `m` of the second alphabet (`Γ = {0, ..., m - 1}`), the
function `h : Σ → Γ` as the list `[h 0, ..., h (k - 1)]`, and the string `w`. -/
abbrev QuasiRealTimeLanguageMembershipInstance :=
  ℕ × GrammarData × GrammarData × GrammarData × ℕ × List ℕ × List ℕ

/-- A right-hand side symbol as a symbol of `Cslib.Language.EncodedCFG`: `Sum.inl B` is
nonterminal `B` and `Sum.inr a` is terminal `a`. -/
def toSum : Bool × ℕ → ℕ ⊕ ℕ
  | (false, B) => .inl B
  | (true, a) => .inr a

/-- The grammar a `GrammarData` denotes, as a `Cslib.Language.EncodedCFG` over the terminals
`ℕ`. -/
def toEncodedCFG (g : GrammarData) : Cslib.Language.EncodedCFG ℕ :=
  ⟨g.2.1, g.2.2.map fun p => (p.1, p.2.map toSum)⟩

/-- A grammar is well-formed over `k` terminals when its initial symbol is one of its `n`
nonterminals and every production has its left-hand side among the nonterminals, and every
right-hand side symbol is a nonterminal below `n` or a terminal below `k`. -/
def GrammarWellFormed (k : ℕ) (g : GrammarData) : Prop :=
  g.2.1 < g.1 ∧ ∀ p ∈ g.2.2, p.1 < g.1 ∧ ∀ x ∈ p.2, if x.1 then x.2 < k else x.2 < g.1

/-- Well-formedness of an instance: the three grammars are well-formed over
`Σ = {0, ..., k - 1}`, `h` has one value for each letter of `Σ`, and the values of `h` and
the letters of `w` lie in `Γ = {0, ..., m - 1}`. -/
def WellFormed : QuasiRealTimeLanguageMembershipInstance → Prop
  | (k, g₁, g₂, g₃, m, h, w) =>
    GrammarWellFormed k g₁ ∧ GrammarWellFormed k g₂ ∧ GrammarWellFormed k g₃ ∧
      h.length = k ∧ (∀ c ∈ h, c < m) ∧ ∀ c ∈ w, c < m

/-- `w` is the letter-by-letter image under `h` of a word over `Σ` that all three grammars
generate. -/
def QuasiRealTimeLanguageMembershipFeasible :
    QuasiRealTimeLanguageMembershipInstance → Prop
  | (k, g₁, g₂, g₃, _, h, w) =>
    ∃ x : List ℕ, (∀ a ∈ x, a < k) ∧
      x ∈ (toEncodedCFG g₁).language ∧ x ∈ (toEncodedCFG g₂).language ∧
      x ∈ (toEncodedCFG g₃).language ∧ x.map (fun a => h.getD a 0) = w

open Classical in
/-- QUASI-REAL-TIME LANGUAGE MEMBERSHIP as a decision problem over bitstrings. -/
noncomputable def quasiRealTimeLanguageMembershipDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuasiRealTimeLanguageMembershipInstance) x with
  | some i => decide (WellFormed i ∧ QuasiRealTimeLanguageMembershipFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembership
