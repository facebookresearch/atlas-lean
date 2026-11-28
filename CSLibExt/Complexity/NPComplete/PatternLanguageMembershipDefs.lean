/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATTERN LANGUAGE MEMBERSHIP: definitions

Source:
D. Angluin, "Finding patterns common to a set of strings", Journal of Computer and System
Sciences 21(1) (1980), 46-62, doi:10.1016/0022-0000(80)90041-0;
A. Ehrenfeucht and G. Rozenberg, "Finding a homomorphism between two words is NP-complete",
Information Processing Letters 9(2) (1979), 86-88, doi:10.1016/0020-0190(79)90135-2;
both recorded in M. L. Schmid, *The Membership Problem of Pattern Languages and Related
Topics*, PhD thesis, Loughborough University (2012), Theorem 2.7 (the membership problem for
nonerasing pattern languages is NP-complete for `Σ = {a, b}`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PatternLanguageMembership

/-- An instance: the pattern (symbols `(isVariable, name)`) and the word. -/
abbrev PatternLanguageMembershipInstance := List (Bool × ℕ) × List ℕ

/-- The image of the pattern `α` under the substitution `σ`: each variable `x` is replaced by
`σ x` and each terminal `a` by itself. -/
def substitute (σ : ℕ → List ℕ) (α : List (Bool × ℕ)) : List ℕ :=
  α.flatMap fun t => if t.1 then σ t.2 else [t.2]

/-- Well-formedness of an instance: the pattern is nonempty. -/
def WellFormed (i : PatternLanguageMembershipInstance) : Prop := i.1 ≠ []

/-- Some nonerasing substitution maps the pattern onto the word. -/
def PatternLanguageMembershipFeasible (i : PatternLanguageMembershipInstance) : Prop :=
  ∃ σ : ℕ → List ℕ, (∀ t ∈ i.1, t.1 = true → σ t.2 ≠ []) ∧ substitute σ i.1 = i.2

open Classical in
/-- PATTERN LANGUAGE MEMBERSHIP as a decision problem over bitstrings. -/
noncomputable def patternLanguageMembershipDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PatternLanguageMembershipInstance) x with
  | some i => decide (WellFormed i ∧ PatternLanguageMembershipFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PatternLanguageMembership
