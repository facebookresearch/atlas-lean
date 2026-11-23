/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidability of Presburger arithmetic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Arithmetic
public import CSLibExt.Logics.FirstOrder.Consistency
public import Mathlib.Computability.RE
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.PresburgerWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

/-- Function symbols of Presburger arithmetic: `0`, `S`, `+`. -/
inductive PresburgerFunctions : ℕ → Type
  /-- The constant `0`. -/
  | zero : PresburgerFunctions 0
  /-- The successor function `S`. -/
  | succ : PresburgerFunctions 1
  /-- Addition. -/
  | add : PresburgerFunctions 2

/-- Relation symbols of Presburger arithmetic: `<` only. -/
inductive PresburgerRelations : ℕ → Type
  /-- Less-than, binary. -/
  | lt : PresburgerRelations 2

/-- The first-order language of Presburger arithmetic: function symbols `0`, `S`, `+` and
the relation `<`. Multiplication is deliberately absent. -/
def PresburgerLanguage : FirstOrder.Language where
  Functions := PresburgerFunctions
  Relations := PresburgerRelations

namespace Presburger

/-- The term `S x` where `x` is the outermost bound variable. -/
def succBvar {α : Type*} : PresburgerLanguage.Term (α ⊕ Fin 1) :=
  Term.func .succ ![Term.var (Sum.inr (0 : Fin 1))]

/-- The bound variable `i` as a term, in a context with `n` bound variables in scope. -/
def bvar {n : ℕ} (i : Fin n) : PresburgerLanguage.Term (Empty ⊕ Fin n) :=
  Term.var (Sum.inr i)

/-- The term `0` with no bound variables, viewed in a context with `n` bound variables. -/
def zeroTermBound {n : ℕ} : PresburgerLanguage.Term (Empty ⊕ Fin n) :=
  Term.func .zero fun i => i.elim0

/-- The term `0` with free variables of any type. -/
def zeroTerm {α : Type*} : PresburgerLanguage.Term α :=
  Term.func .zero fun i => i.elim0

/-- The successor of a term in a bounded context. -/
def tSucc {n : ℕ} (t : PresburgerLanguage.Term (Empty ⊕ Fin n)) :
    PresburgerLanguage.Term (Empty ⊕ Fin n) :=
  Term.func .succ ![t]

/-- The sum of two terms in a bounded context. -/
def tAdd {n : ℕ} (s t : PresburgerLanguage.Term (Empty ⊕ Fin n)) :
    PresburgerLanguage.Term (Empty ⊕ Fin n) :=
  Term.func .add ![s, t]

/-- Equality of two terms as a bounded formula. -/
def eqF {n : ℕ} (s t : PresburgerLanguage.Term (Empty ⊕ Fin n)) :
    PresburgerLanguage.BoundedFormula Empty n :=
  BoundedFormula.equal s t

/-- Less-than of two terms as a bounded formula. -/
def ltF {n : ℕ} (s t : PresburgerLanguage.Term (Empty ⊕ Fin n)) :
    PresburgerLanguage.BoundedFormula Empty n :=
  BoundedFormula.rel .lt ![s, t]

/-- P1: `∀x. ¬ S x = 0`. -/
def axiomSuccNeZero : PresburgerLanguage.Sentence :=
  ((eqF (tSucc (bvar (0 : Fin 1))) zeroTermBound).not).all

/-- P2: `∀x ∀y. S x = S y → x = y`. -/
def axiomSuccInjective : PresburgerLanguage.Sentence :=
  ((eqF (tSucc (bvar (0 : Fin 2))) (tSucc (bvar (1 : Fin 2)))).imp
    (eqF (bvar (0 : Fin 2)) (bvar (1 : Fin 2)))).all.all

/-- P3: `∀x. x + 0 = x`. -/
def axiomAddZero : PresburgerLanguage.Sentence :=
  (eqF (tAdd (bvar (0 : Fin 1)) zeroTermBound) (bvar (0 : Fin 1))).all

/-- P4: `∀x ∀y. x + S y = S (x + y)`. -/
def axiomAddSucc : PresburgerLanguage.Sentence :=
  (eqF (tAdd (bvar (0 : Fin 2)) (tSucc (bvar (1 : Fin 2))))
    (tSucc (tAdd (bvar (0 : Fin 2)) (bvar (1 : Fin 2))))).all.all

/-- P5: `∀x. ¬ x < 0`. -/
def axiomNotLtZero : PresburgerLanguage.Sentence :=
  ((ltF (bvar (0 : Fin 1)) zeroTermBound).not).all

/-- P6: `∀x ∀y. x < S y ↔ (x < y ∨ x = y)`. -/
def axiomLtSucc : PresburgerLanguage.Sentence :=
  (((ltF (bvar (0 : Fin 2)) (tSucc (bvar (1 : Fin 2)))).iff
    ((ltF (bvar (0 : Fin 2)) (bvar (1 : Fin 2))).not.imp
      (eqF (bvar (0 : Fin 2)) (bvar (1 : Fin 2)))))).all.all

/-- P7: `∀x ∀y. x < y ∨ x = y ∨ y < x` (trichotomy). -/
def axiomTrichotomy : PresburgerLanguage.Sentence :=
  ((ltF (bvar (0 : Fin 2)) (bvar (1 : Fin 2))).not.imp
    ((eqF (bvar (0 : Fin 2)) (bvar (1 : Fin 2))).not.imp
      (ltF (bvar (1 : Fin 2)) (bvar (0 : Fin 2))))).all.all

/-- The induction axiom for a body `φ` with `k` parameters, where `φ : BoundedFormula
(Fin k) 1` has one bound variable (the induction variable `x`) and `k` free variables
(the parameters `y⃗`):
`∀y⃗ [φ(0, y⃗) → (∀x (φ(x, y⃗) → φ(S x, y⃗))) → ∀x φ(x, y⃗)]`.
The body is built with the parameters free, then `BoundedFormula.relabel` turns the
parameters into bound variables and `.alls` universally closes over them. This is the
standard induction schema with parameters, as in the textbook.
Source: H. Enderton, A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001,
§3.2. -/
def inductionAxiom {k : ℕ} (φ : PresburgerLanguage.BoundedFormula (Fin k) 1) :
    PresburgerLanguage.Sentence :=
  (((instantiate zeroTerm φ).relabel (Sum.inr : Fin k → Empty ⊕ Fin k)).imp
    ((((φ.imp (substBoundFormula succBvar φ)).all).relabel
      (Sum.inr : Fin k → Empty ⊕ Fin k)).imp
      (φ.all.relabel (Sum.inr : Fin k → Empty ⊕ Fin k)))).alls

/-- Presburger arithmetic: the seven axioms above together with the induction axiom for
every body with any number `k` of parameters. -/
def PresburgerTheory : PresburgerLanguage.Theory :=
  {axiomSuccNeZero, axiomSuccInjective, axiomAddZero, axiomAddSucc, axiomNotLtZero,
    axiomLtSucc, axiomTrichotomy} ∪ ⋃ k : ℕ, Set.range (inductionAxiom (k := k))

end Presburger

/-- Gödel numbering of Presburger function symbols, via constructor tags. -/
def codeFun {l : ℕ} : PresburgerFunctions l → ℕ
  | .zero => 0
  | .succ => 1
  | .add => 2

/-- Gödel numbering of a tuple of codes, via Cantor pairing. -/
def codeTuple : ∀ {l : ℕ}, (Fin l → ℕ) → ℕ
  | 0, _ => 0
  | l + 1, xs => Nat.pair (codeTuple (Fin.init xs)) (xs (Fin.last l))

/-- Gödel numbering of Presburger terms with `n` bound variables in scope, via Cantor
pairing: variables by tag `1` plus index, function applications by tag `2` plus the
function tag and the tuple code of the argument codes. -/
def codeTerm {n : ℕ} : PresburgerLanguage.Term (Empty ⊕ Fin n) → ℕ
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr i) => Nat.pair 1 i.val
  | .func f ts => Nat.pair 2 (Nat.pair (codeFun f) (codeTuple fun i => codeTerm (ts i)))

/-- Gödel numbering of Presburger relation symbols. -/
def codeRel {l : ℕ} : PresburgerRelations l → ℕ
  | .lt => 0

/-- Gödel numbering of Presburger formulas with `n` bound variables in scope, via Cantor
pairing with distinct tags per constructor. The tags make the numbering injective, and
it is primitive-recursive (built from pairing and structural recursion) and computably
decodable by unpairing. -/
def codeFormula {n : ℕ} : PresburgerLanguage.BoundedFormula Empty n → ℕ
  | .falsum => 0
  | .equal t₁ t₂ => Nat.pair 1 (Nat.pair (codeTerm t₁) (codeTerm t₂))
  | .rel R ts => Nat.pair 2 (Nat.pair (codeRel R) (codeTuple fun i => codeTerm (ts i)))
  | .imp φ ψ => Nat.pair 3 (Nat.pair (codeFormula φ) (codeFormula ψ))
  | .all φ => Nat.pair 4 (codeFormula φ)

/-- Gödel numbering of Presburger sentences. -/
def codeSentence : PresburgerLanguage.Sentence → ℕ := codeFormula

/-- Presburger provability over the infinite free-variable type `ℕ`: Presburger's
sentences, embedded as formulas over `ℕ` by `Formula.relabel Empty.elim`, prove a
sentence relabeled the same way. Stating provability over the sentence type itself
(`Provable PresburgerTheory`) would instantiate the calculus's free-variable type as
`Empty`, and `Derivable.allI` needs an eigenvariable of that type, so universal
introduction would be unavailable and the relation would not be theoremhood in
Presburger arithmetic. The relabeled form is the repository's standard provability
for theories (`Completeness.lean`, `Provable.models`, `provable_iff_models`), and it
is sound and complete for semantic consequence over `PresburgerTheory`. -/
abbrev PresburgerProvable (φ : PresburgerLanguage.Sentence) : Prop :=
  Provable (Formula.relabel (Empty.elim : Empty → ℕ) '' Presburger.PresburgerTheory)
    (Formula.relabel (Empty.elim : Empty → ℕ) φ)

/-- Decidability of Presburger arithmetic: the set of Gödel codes of sentences provable
from the Presburger axioms is computable. Provability is `PresburgerProvable` above,
over the infinite free-variable type `ℕ`. The statement is a `ComputablePred` over
`ℕ` via the explicit Gödel numbering `codeSentence`: a bare `∃ dec : Sentence → Bool`
would not express algorithmic decidability, since classical choice supplies a
characteristic function for every predicate. The standard proof is quantifier
elimination (see `PresburgerQuantifierEliminationWanted.lean`): every formula is
provably equivalent to a quantifier-free one, and quantifier-free sentences are
decidable by evaluating the finitely many atomic comparisons.
Source: M. Presburger, "Über die Vollständigkeit eines gewissen Systems der Arithmetik
ganzer Zahlen in welchem die Addition die einzige Operation ist", in Comptes Rendus du
I Congrès des Mathématiciens des Pays Slaves, Warsaw, 1929, 92-101; see also H. Enderton,
A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §3.2, and G. Boolos,
J. Burgess, R. Jeffrey, Computability and Logic, 5th ed., Cambridge University Press,
2007, Chapter 28. -/
public theorem_wanted presburger_decidable :
    ComputablePred (fun n : ℕ => ∃ φ : PresburgerLanguage.Sentence,
      codeSentence φ = n ∧ PresburgerProvable φ)

end Cslib.Logic.PresburgerWanted
