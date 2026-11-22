/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MODAL LOGIC S5-SATISFIABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO13] MODAL LOGIC
S5-SATISFIABILITY;
R. E. Ladner, "The computational complexity of provability in systems of modal
propositional logic", SIAM Journal on Computing 6 (1977), 467-480,
doi:10.1137/0206033.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Modal.Kripke

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ModalLogicS5Satisfiability

open Cslib.Modal

/-!
# MODAL LOGIC S5-SATISFIABILITY is NP-complete

INSTANCE: a set `U` of variables and a modal formula `A` over `U`, built from the variables
with `∧`, `¬` and the necessity operator `□`. QUESTION: is `A` S5-satisfiable, that is, true at
some world of a Kripke model whose accessibility relation is an equivalence relation?

The variables are `u₀, ..., u_{n-1}`. The formula is written in postfix (reverse Polish)
notation as a list of tokens: `0` is `∧` (binary), `1` is `¬`, `2` is `□` (unary), and `k + 3`
is the variable `uₖ`. `parse` reads the tokens with a stack into the repository's modal
formulas `Cslib.Modal.Formula ℕ`, with `∧` and `¬` as `Formula.and` and `Formula.neg`; a
token list is a formula exactly when `parse` returns one. Satisfaction is
`Cslib.Modal.KripkeModel.Satisfies`, and the models of S5 are those whose relation is an
`Equivalence`, as in `Cslib.Modal.satisfiable_S5`.

Ladner proves that non-provability in S5 is NP-complete; by the completeness of S5 for
equivalence models, `A` is S5-satisfiable exactly when `¬A` is not S5-provable.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables and the formula as a postfix token list. -/
abbrev ModalLogicS5SatisfiabilityInstance := ℕ × List ℕ

/-- Read a postfix token list onto a stack of formulas: `0` pops `ψ` and `φ` and pushes
`φ ∧ ψ`, `1` pops `φ` and pushes `¬φ`, `2` pops `φ` and pushes `□φ`, and `k + 3` pushes the
variable `uₖ`. The result is the single formula left on the stack, or `none` when a token
lacks its operands or more than one formula is left. -/
def parse : List ℕ → List (Formula ℕ) → Option (Formula ℕ)
  | [], [φ] => some φ
  | [], _ => none
  | 0 :: rest, ψ :: φ :: stack => parse rest (Formula.and φ ψ :: stack)
  | 1 :: rest, φ :: stack => parse rest (Formula.neg φ :: stack)
  | 2 :: rest, φ :: stack => parse rest (Formula.box φ :: stack)
  | (k + 3) :: rest, stack => parse rest (Formula.atom k :: stack)
  | _ :: _, _ => none

/-- Well-formedness of an instance: the tokens form a formula, and every variable token names
one of the `n` variables. -/
def WellFormed (i : ModalLogicS5SatisfiabilityInstance) : Prop :=
  (parse i.2 []).isSome ∧ ∀ t ∈ i.2, 3 ≤ t → t - 3 < i.1

/-- The formula is true at some world of a Kripke model whose relation is an equivalence. -/
def ModalLogicS5SatisfiabilityFeasible (i : ModalLogicS5SatisfiabilityInstance) : Prop :=
  ∃ φ, parse i.2 [] = some φ ∧
    ∃ (W : Type) (M : KripkeModel W ℕ) (w : W), Equivalence M.rel ∧ M.Satisfies w φ

open Classical in
/-- MODAL LOGIC S5-SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def modalLogicS5SatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ModalLogicS5SatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ ModalLogicS5SatisfiabilityFeasible i)
  | none => false

/-- **MODAL LOGIC S5-SATISFIABILITY is NP-complete.** Source: Garey and Johnson (1979), [LO13];
Ladner (1977). -/
public theorem_wanted modalLogicS5Satisfiability_npComplete :
    modalLogicS5SatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L modalLogicS5SatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.ModalLogicS5Satisfiability
