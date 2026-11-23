/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Church's theorem: first-order validity is undecidable
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Arithmetic
public import Mathlib.Computability.RE

@[expose] public section

namespace Cslib.Logic.ChurchWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

/-- Gödel numbering of arithmetic function symbols, via constructor tags. -/
def codeFun {l : ℕ} : ArithmeticFunctions l → ℕ
  | .zero => 0
  | .succ => 1
  | .add => 2
  | .mul => 3

/-- Gödel numbering of a tuple of codes, via Cantor pairing. -/
def codeTuple : ∀ {l : ℕ}, (Fin l → ℕ) → ℕ
  | 0, _ => 0
  | l + 1, xs => Nat.pair (codeTuple (Fin.init xs)) (xs (Fin.last l))

/-- Gödel numbering of arithmetic terms with `n` bound variables in scope, via Cantor
pairing: variables by tag `1` plus index, function applications by tag `2` plus the
function tag and the tuple code of the argument codes. -/
def codeTerm {n : ℕ} : ArithmeticLanguage.Term (Empty ⊕ Fin n) → ℕ
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr i) => Nat.pair 1 i.val
  | .func f ts => Nat.pair 2 (Nat.pair (codeFun f) (codeTuple fun i => codeTerm (ts i)))

/-- Gödel numbering of arithmetic formulas with `n` bound variables in scope, via Cantor
pairing with distinct tags per constructor. The language has no relation symbols besides
equality, so the `rel` case is vacuous. The tags make the numbering injective, and it is
primitive-recursive (built from pairing and structural recursion) and computably
decodable by unpairing. -/
def codeFormula {n : ℕ} : ArithmeticLanguage.BoundedFormula Empty n → ℕ
  | .falsum => 0
  | .equal t₁ t₂ => Nat.pair 1 (Nat.pair (codeTerm t₁) (codeTerm t₂))
  | .rel R _ => R.elim
  | .imp φ ψ => Nat.pair 2 (Nat.pair (codeFormula φ) (codeFormula ψ))
  | .all φ => Nat.pair 3 (codeFormula φ)

/-- Gödel numbering of arithmetic sentences. -/
def codeSentence : ArithmeticLanguage.Sentence → ℕ := codeFormula

/-- Church's theorem: validity of first-order sentences in the language of arithmetic is
undecidable. The set of Gödel codes of valid sentences is not computable: there is no
computable predicate on `ℕ` that holds exactly on the codes of sentences true in every
structure. The statement is a `ComputablePred` over `ℕ` via the explicit Gödel numbering
`codeSentence`: a bare `¬ ∃ dec : Sentence → Bool` would be false, since classical
choice supplies a characteristic function for every predicate. Validity is quantified
over structures in `Type` only; this is no restriction, since a sentence failing in some
model fails in a countable model by downward Löwenheim–Skolem.
Source: A. Church, "A Note on the Entscheidungsproblem", Journal of Symbolic Logic 1
(1936), 40-41; see also H. Enderton, A Mathematical Introduction to Logic, 2nd ed.,
Academic Press, 2001, §3.5, and M. Sipser, Introduction to the Theory of Computation,
3rd ed., Cengage, 2013, §6.3 (the Entscheidungsproblem). -/
public theorem_wanted church_fol_validity_undecidable :
    ¬ ComputablePred (fun n : ℕ => ∃ φ : ArithmeticLanguage.Sentence,
      codeSentence φ = n ∧ ∀ (M : Type) [ArithmeticLanguage.Structure M], (M ⊨ φ))

end Cslib.Logic.ChurchWanted
