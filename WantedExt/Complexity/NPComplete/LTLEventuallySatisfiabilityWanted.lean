/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LTL(F) SATISFIABILITY is NP-complete

Source:
A. P. Sistla and E. M. Clarke, "The complexity of propositional linear temporal logics",
Journal of the ACM 32 (1985), 733-749, doi:10.1145/3828.3837, Theorem 3.5 (ii).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.LTL.OmegaWord

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LTLEventuallySatisfiability

open Cslib.LTL

/-!
# LTL(F) SATISFIABILITY is NP-complete

INSTANCE: a formula `f` of the propositional linear temporal logic `L(F)`, built from atomic
propositions with `¬`, `∧` and the temporal operator `F` ("eventually"), the only temporal
operator. QUESTION: is `f` satisfiable, that is, true at the first state of some structure, an
ω-sequence of states each labelled with the set of atomic propositions true in it?

Sistla and Clarke (Section 2) define formulas from atomic propositions with `¬`, `∧`, `X`, `U`
and `S`, and `L(F)` as the logic whose only temporal operator is `F`, with `F f = True U f`;
`f U g` holds at state `sᵢ` when `g` holds at some `sₖ` with `k ≥ i` and `f` holds at every
`sⱼ` with `i ≤ j < k`, so `F f` holds at `sᵢ` exactly when `f` holds at some `sₖ` with `k ≥ i`.
Theorem 3.5 (ii) states that satisfiability is NP-complete for `L(F)`.

The formula is written in postfix (reverse Polish) notation as a list of tokens: `0` is `∧`
(binary), `1` is `¬`, `2` is `F` (unary), and `k + 3` is the atomic proposition `Pₖ`. `parse`
reads the tokens with a stack into CSLib's LTL formulas `Cslib.LTL.Formula ℕ`, with `∧`, `¬` and
`F` as `Formula.and`, `Formula.not` and `Formula.eventually` (`Formula.until .top`, the same
abbreviation as the source's); a token list is a formula exactly when `parse` returns one. A
structure is an ω-word `w : Cslib.ωSequence (Set ℕ)` of label sets, and satisfaction is CSLib's
`Cslib.LTL.Word.Satisfies` under the valuation `fun s a => a ∈ s` (an atom holds in a state when
it belongs to the state's label set).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the formula as a postfix token list. -/
abbrev LTLEventuallySatisfiabilityInstance := List ℕ

/-- Read a postfix token list onto a stack of formulas: `0` pops `g` and `f` and pushes
`f ∧ g`, `1` pops `f` and pushes `¬f`, `2` pops `f` and pushes `F f`, and `k + 3` pushes the
atomic proposition `Pₖ`. The result is the single formula left on the stack, or `none` when a
token lacks its operands or more than one formula is left. -/
def parse : List ℕ → List (Formula ℕ) → Option (Formula ℕ)
  | [], [f] => some f
  | [], _ => none
  | 0 :: rest, g :: f :: stack => parse rest (Formula.and f g :: stack)
  | 1 :: rest, f :: stack => parse rest (Formula.not f :: stack)
  | 2 :: rest, f :: stack => parse rest (Formula.eventually f :: stack)
  | (k + 3) :: rest, stack => parse rest (Formula.atom k :: stack)
  | _ :: _, _ => none

/-- Well-formedness of an instance: the tokens form an `L(F)` formula. -/
def WellFormed (i : LTLEventuallySatisfiabilityInstance) : Prop :=
  (parse i []).isSome

/-- The formula holds at the first state of some ω-sequence of label sets. -/
def LTLEventuallySatisfiabilityFeasible (i : LTLEventuallySatisfiabilityInstance) : Prop :=
  ∃ f, parse i [] = some f ∧
    ∃ w : Cslib.ωSequence (Set ℕ), Word.Satisfies (fun s a => a ∈ s) w f

open Classical in
/-- LTL(F) SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def ltlEventuallySatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LTLEventuallySatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ LTLEventuallySatisfiabilityFeasible i)
  | none => false

/-- **LTL(F) SATISFIABILITY is NP-complete.** Source: Sistla and Clarke (1985),
Theorem 3.5 (ii). -/
public theorem_wanted ltlEventuallySatisfiability_npComplete :
    ltlEventuallySatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ltlEventuallySatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.LTLEventuallySatisfiability
