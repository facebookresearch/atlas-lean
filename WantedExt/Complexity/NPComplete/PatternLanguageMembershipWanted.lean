/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATTERN LANGUAGE MEMBERSHIP is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PatternLanguageMembership

/-!
# PATTERN LANGUAGE MEMBERSHIP is NP-complete

INSTANCE: a pattern `α`, a nonempty string over `Σ ∪ X` with terminal symbols `Σ` and variables
`X`, and a word `w` over `Σ`.
QUESTION: is `w` in the (nonerasing) pattern language of `α`, that is, is there a substitution
`h` (a morphism with `h(a) = a` for every terminal `a`) that maps every variable to a nonempty
word and satisfies `h(α) = w`?

Terminals and variables are natural numbers: a pattern symbol `(false, a)` is the terminal `a`
and `(true, x)` is the variable `x`. A substitution is a map `σ` from variables to words,
extended to patterns symbol by symbol; each occurrence of a variable is replaced by the same
word. The terminal alphabet is not bounded in the instance; Schmid's Theorem 2.7 gives
NP-hardness already for the binary alphabet, whose instances are a subclass.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PATTERN LANGUAGE MEMBERSHIP is NP-complete.** Source: Angluin (1980); Ehrenfeucht and
Rozenberg (1979). -/
public theorem_wanted patternLanguageMembership_npComplete :
    patternLanguageMembershipDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L patternLanguageMembershipDec

end MetaMathlibExt.Complexity.NPComplete.PatternLanguageMembership
