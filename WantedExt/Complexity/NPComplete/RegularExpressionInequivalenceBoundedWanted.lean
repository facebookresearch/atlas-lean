/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR EXPRESSION INEQUIVALENCE for bounded languages is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 267, comment to problem
[AL9] REGULAR EXPRESSION INEQUIVALENCE ("Also NP-complete if one
or both of E₁ and E₂ represent bounded languages");
H. B. Hunt III, D. J. Rosenkrantz, and T. G. Szymanski, "On the equivalence,
containment, and covering problems for the regular and context-free languages",
Journal of Computer and System Sciences 12 (1976), 222-268,
doi:10.1016/S0022-0000(76)80038-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Languages.KleeneConverse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Computability.RegularExpressions

@[expose] public section

open scoped Computability

namespace MetaMathlibExt.Complexity.NPComplete.RegularExpressionInequivalenceBounded

/-!
# REGULAR EXPRESSION INEQUIVALENCE for bounded languages is NP-complete

INSTANCE: regular expressions `E₁` and `E₂` over the operators `{∪, ·, *}` and the
alphabet `Σ`, one or both of which represent bounded languages. QUESTION: do `E₁` and `E₂`
represent different languages?

Regular expressions are those of Garey and Johnson's Section 7.4 (p. 174): `∅`, `ε`, each
letter `a ∈ Σ`, and `α + β`, `αβ`, `α*` for regular expressions `α`, `β`; these are Mathlib's
`RegularExpression`, and the language of `E` is `E.matches'`. The alphabet is `Σ = {0, ..., m - 1}`.
A language `L` is bounded when `L ⊆ w₁* w₂* ⋯ w_k*` for some strings `w₁, ..., w_k` (Hunt,
Rosenkrantz, and Szymanski, Definition 1.4; `IsBounded`). An expression is written
in postfix (reverse Polish) notation as a list of tokens: `(0, 0)` is `∅`, `(1, 0)` is `ε`,
`(2, a)` is the letter `a`, and `(3, 0)`, `(4, 0)`, `(5, 0)` are `+`, concatenation and `*`
applied to the expressions before them. A token list that does not spell exactly one
expression is malformed. Postfix spelling keeps the input length proportional to the length of
the expression; `Cslib.Language.EncodedRegex` is not used because its node lists may share
subexpressions, which can make an expression exponentially shorter than its written form.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- One postfix token read onto a stack of regular expressions: `(0, 0)` pushes `∅`, `(1, 0)`
pushes `ε`, `(2, a)` pushes the letter `a`; `(3, 0)` and `(4, 0)` replace the top two
expressions `α`, `β` (`β` on top) by `α + β` and `αβ`; `(5, 0)` replaces the top expression `α`
by `α*`. Any other token, or too short a stack, fails. -/
def readToken : List (RegularExpression ℕ) → ℕ × ℕ → Option (List (RegularExpression ℕ))
  | s, (0, 0) => some (0 :: s)
  | s, (1, 0) => some (1 :: s)
  | s, (2, a) => some (.char a :: s)
  | q :: p :: s, (3, 0) => some ((p + q) :: s)
  | q :: p :: s, (4, 0) => some ((p * q) :: s)
  | p :: s, (5, 0) => some (p.star :: s)
  | _, _ => none

/-- The regular expression a postfix token list spells, if it spells exactly one. -/
def parse (toks : List (ℕ × ℕ)) : Option (RegularExpression ℕ) :=
  match toks.foldlM readToken [] with
  | some [r] => some r
  | _ => none

/-- `toks` spells the regular expression `E`, all of whose letters are below `m`. -/
def ExprOver (m : ℕ) (toks : List (ℕ × ℕ)) (E : RegularExpression ℕ) : Prop :=
  parse toks = some E ∧ ∀ a ∈ Cslib.Language.KleeneConverse.regexLetters E, a < m

/-- A bounded language (Hunt, Rosenkrantz, and Szymanski (1976), Definition 1.4): there are
strings `w₁, ..., w_k` with `L ⊆ w₁* w₂* ⋯ w_k*`. -/
def IsBounded (L : Language ℕ) : Prop :=
  ∃ ws : List (List ℕ), L ≤ (ws.map fun w => ({w} : Language ℕ)∗).prod

/-- An instance: the alphabet size `m` (letters `0, ..., m - 1`) and the postfix token lists of
`E₁` and `E₂`. -/
abbrev RegularExpressionInequivalenceBoundedInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- Well-formedness of an instance: the token lists spell regular expressions `E₁` and `E₂` over
the alphabet, and at least one of them represents a bounded language. -/
def WellFormed (i : RegularExpressionInequivalenceBoundedInstance) : Prop :=
  ∃ E₁ E₂, ExprOver i.1 i.2.1 E₁ ∧ ExprOver i.1 i.2.2 E₂ ∧
    (IsBounded E₁.matches' ∨ IsBounded E₂.matches')

/-- `E₁` and `E₂` represent different languages. -/
def RegularExpressionInequivalenceBoundedFeasible
    (i : RegularExpressionInequivalenceBoundedInstance) : Prop :=
  ∃ E₁ E₂, parse i.2.1 = some E₁ ∧ parse i.2.2 = some E₂ ∧ E₁.matches' ≠ E₂.matches'

open Classical in
/-- REGULAR EXPRESSION INEQUIVALENCE for bounded languages as a decision problem over bitstrings. -/
noncomputable def regularExpressionInequivalenceBoundedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RegularExpressionInequivalenceBoundedInstance) x with
  | some i => decide (WellFormed i ∧ RegularExpressionInequivalenceBoundedFeasible i)
  | none => false

/-- **REGULAR EXPRESSION INEQUIVALENCE for bounded languages is NP-complete.** Source: Garey and
Johnson (1979), [AL9] comment; Hunt, Rosenkrantz, and Szymanski (1976). -/
public theorem_wanted regularExpressionInequivalenceBounded_npComplete :
    regularExpressionInequivalenceBoundedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L regularExpressionInequivalenceBoundedDec

end MetaMathlibExt.Complexity.NPComplete.RegularExpressionInequivalenceBounded
