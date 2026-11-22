/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# String constraints: syntax and semantics
-/
module

public import CSLibExt.Computability.Decidability.RegularExpression
public import Mathlib.Data.List.Basic

/-!
# String constraints: syntax and semantics

A **string constraint** is a *positive* Boolean combination of atoms
over string terms: conjunctions and disjunctions, with no negation.
A term is a constant word, a variable, the concatenation of two
terms, or a letter-to-word morphism applied to a term (a
single-state transducer; general finite-state transducers are not
formalized); an atom is a word equation between terms, a
regular-language membership test for a term, or a bound on the length
of a term. Assignments map variables to words (`List α`).

This is the positive fragment of the constraint language of the
string solvers in the references below: HAMPI handles word equations,
regular membership and (in its TOSEM form) context-free membership;
Z3str2 and Z3str3 handle word equations, regular membership and
length constraints. Negation, disequality, negated membership, and
negated length bounds are not formalized here, and neither is
context-free membership.

## Main results

- `Term`, `Atom`, `Formula`: the syntax.
- `eval`, `SatAtom`, `Sat`: the semantics.
- `satAtomB`, `satB`, `satB_iff`: a Boolean checker for satisfaction,
  proved correct. Regular membership is checked with the existing
  `Cslib.Language.EncodedRegex.memB` decider, so no new regular-language
  representation is introduced.
- `eval_eq_of_agree_on_vars`, `sat_congr`: evaluation and satisfaction
  depend only on the variables occurring in the term or formula.

## References

* A. Kieżun, V. Ganesh, S. Artzi, P. J. Guo, P. Hooimeijer, M. D. Ernst,
  *HAMPI: A Solver for Word Equations over Strings, Regular
  Expressions, and Context-Free Grammars*, ACM TOSEM 21(4), Nov 2012,
  pp. 25:1–25:28.
* Y. Zheng, V. Ganesh, et al., *Effective Search-space Pruning for
  Solvers of String Equations, Regular Expressions and Length
  Constraints* (Z3str2), CAV 2015.
* M. Berzish, V. Ganesh, Y. Zheng, *Z3str3: A String Solver with
  Theory-aware Heuristics*, FMCAD 2017.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

open Cslib.Language

variable {α : Type*} {V : Type*}

/-- A **string term** over variables `V`: a constant word, a variable,
the concatenation of two terms, or a letter-to-word morphism applied
to a term. -/
inductive Term (α : Type*) (V : Type*) where
  | const : List α → Term α V
  | var : V → Term α V
  | append : Term α V → Term α V → Term α V
  | hom : (α → List α) → Term α V → Term α V

/-- Evaluation of a term under an assignment. -/
def eval (σ : V → List α) : Term α V → List α
  | .const w => w
  | .var i => σ i
  | .append t₁ t₂ => eval σ t₁ ++ eval σ t₂
  | .hom f t => (eval σ t).flatMap f

@[simp] theorem eval_const (σ : V → List α) (w : List α) :
    eval σ (Term.const w : Term α V) = w := rfl

@[simp] theorem eval_var (σ : V → List α) (i : V) :
    eval σ (Term.var i : Term α V) = σ i := rfl

@[simp] theorem eval_append (σ : V → List α) (t₁ t₂ : Term α V) :
    eval σ (Term.append t₁ t₂) = eval σ t₁ ++ eval σ t₂ := rfl

@[simp] theorem eval_hom (σ : V → List α) (f : α → List α) (t : Term α V) :
    eval σ (Term.hom f t) = (eval σ t).flatMap f := rfl

/-- The variables occurring in a term, as a list (duplicates allowed). -/
def varsOf : Term α V → List V
  | .const _ => []
  | .var i => [i]
  | .append t₁ t₂ => varsOf t₁ ++ varsOf t₂
  | .hom _ t => varsOf t

@[simp] theorem varsOf_const (w : List α) :
    varsOf (Term.const w : Term α V) = [] := rfl

@[simp] theorem varsOf_var (i : V) :
    varsOf (Term.var i : Term α V) = [i] := rfl

@[simp] theorem varsOf_append (t₁ t₂ : Term α V) :
    varsOf (Term.append t₁ t₂) = varsOf t₁ ++ varsOf t₂ := rfl

@[simp] theorem varsOf_hom (f : α → List α) (t : Term α V) :
    varsOf (Term.hom f t) = varsOf t := rfl

/-- Evaluation depends only on the values of the variables in the term. -/
theorem eval_eq_of_agree_on_vars {σ τ : V → List α} {t : Term α V}
    (h : ∀ i ∈ varsOf t, σ i = τ i) : eval σ t = eval τ t := by
  induction t with
  | const _ => rfl
  | var i => exact h i (by simp)
  | append t₁ t₂ ih₁ ih₂ =>
    simp only [eval_append, ih₁ (fun i hi => h i (by simp [hi])),
      ih₂ (fun i hi => h i (by simp [hi]))]
  | hom f t ih =>
    change (eval σ t).flatMap f = (eval τ t).flatMap f
    rw [ih (fun i hi => h i (by simp [hi]))]

/-- A **string atom**: a word equation, a regular-membership test, or a
length bound. Regular languages are represented by the existing
`Cslib.Language.EncodedRegex`. -/
inductive Atom (α : Type*) (V : Type*) where
  | eq : Term α V → Term α V → Atom α V
  | mem : Term α V → EncodedRegex α → Atom α V
  | lenLe : Term α V → ℕ → Atom α V
  | lenGe : Term α V → ℕ → Atom α V

/-- The variables occurring in an atom. -/
def varsOfAtom : Atom α V → List V
  | .eq t₁ t₂ => varsOf t₁ ++ varsOf t₂
  | .mem t _ => varsOf t
  | .lenLe t _ => varsOf t
  | .lenGe t _ => varsOf t

/-- **String formulas**: positive Boolean combinations of atoms
(conjunction, disjunction, `true`, `false`; no negation), as in the
positive fragment of SMT-LIB assertions. -/
inductive Formula (α : Type*) (V : Type*) where
  | atom : Atom α V → Formula α V
  | and : Formula α V → Formula α V → Formula α V
  | or : Formula α V → Formula α V → Formula α V
  | true : Formula α V
  | false : Formula α V

/-- Conjunction of a list of formulas. -/
def andChain : List (Formula α V) → Formula α V
  | [] => .true
  | f :: fs => .and f (andChain fs)

/-- Disjunction of a list of formulas. -/
def orChain : List (Formula α V) → Formula α V
  | [] => .false
  | f :: fs => .or f (orChain fs)

/-- The variables occurring in a formula. -/
def varsOfFormula : Formula α V → List V
  | .atom a => varsOfAtom a
  | .and f g => varsOfFormula f ++ varsOfFormula g
  | .or f g => varsOfFormula f ++ varsOfFormula g
  | .true => []
  | .false => []

/-- Satisfaction of an atom under an assignment. -/
def SatAtom (σ : V → List α) : Atom α V → Prop
  | .eq t₁ t₂ => eval σ t₁ = eval σ t₂
  | .mem t e => eval σ t ∈ e.toRegex.matches'
  | .lenLe t k => (eval σ t).length ≤ k
  | .lenGe t k => k ≤ (eval σ t).length

/-- Satisfaction of a formula under an assignment. -/
def Sat (σ : V → List α) : Formula α V → Prop
  | .atom a => SatAtom σ a
  | .and f g => Sat σ f ∧ Sat σ g
  | .or f g => Sat σ f ∨ Sat σ g
  | .true => True
  | .false => False

@[simp] theorem sat_atom (σ : V → List α) (a : Atom α V) :
    Sat σ (Formula.atom a) ↔ SatAtom σ a := Iff.rfl

@[simp] theorem sat_and (σ : V → List α) (f g : Formula α V) :
    Sat σ (Formula.and f g) ↔ Sat σ f ∧ Sat σ g := Iff.rfl

@[simp] theorem sat_or (σ : V → List α) (f g : Formula α V) :
    Sat σ (Formula.or f g) ↔ Sat σ f ∨ Sat σ g := Iff.rfl

@[simp] theorem sat_true (σ : V → List α) : Sat σ (Formula.true : Formula α V) ↔ True :=
  Iff.rfl

@[simp] theorem sat_false (σ : V → List α) :
    Sat σ (Formula.false : Formula α V) ↔ False := Iff.rfl

/-- Satisfaction of a conjunction chain: every member is satisfied. -/
theorem sat_andChain {σ : V → List α} {fs : List (Formula α V)} :
    Sat σ (andChain fs) ↔ ∀ f ∈ fs, Sat σ f := by
  induction fs with
  | nil => simp [andChain]
  | cons f fs ih =>
    simp only [andChain, sat_and, ih, List.mem_cons, forall_eq_or_imp]

/-- Satisfaction of a disjunction chain: one member is satisfied. -/
theorem sat_orChain {σ : V → List α} {fs : List (Formula α V)} :
    Sat σ (orChain fs) ↔ ∃ f ∈ fs, Sat σ f := by
  induction fs with
  | nil => simp [orChain]
  | cons f fs ih =>
    simp only [orChain, sat_or, ih, List.mem_cons, exists_eq_or_imp]

/-- Satisfaction of an atom depends only on the values of its variables. -/
theorem satAtom_congr {σ τ : V → List α} {a : Atom α V}
    (h : ∀ i ∈ varsOfAtom a, σ i = τ i) : SatAtom σ a ↔ SatAtom τ a := by
  cases a with
  | eq t₁ t₂ =>
    simp only [SatAtom, varsOfAtom, List.mem_append] at h ⊢
    rw [eval_eq_of_agree_on_vars (fun i hi => h i (Or.inl hi)),
      eval_eq_of_agree_on_vars (fun i hi => h i (Or.inr hi))]
  | mem t e =>
    simp only [SatAtom, varsOfAtom] at h ⊢
    rw [eval_eq_of_agree_on_vars h]
  | lenLe t k =>
    simp only [SatAtom, varsOfAtom] at h ⊢
    rw [eval_eq_of_agree_on_vars h]
  | lenGe t k =>
    simp only [SatAtom, varsOfAtom] at h ⊢
    rw [eval_eq_of_agree_on_vars h]

/-- Satisfaction depends only on the values of the variables in the formula. -/
theorem sat_congr {σ τ : V → List α} {φ : Formula α V}
    (h : ∀ i ∈ varsOfFormula φ, σ i = τ i) : Sat σ φ ↔ Sat τ φ := by
  induction φ with
  | atom a => exact satAtom_congr h
  | and f g ihf ihg =>
    simp only [sat_and, ihf (fun i hi => h i (List.mem_append_left _ hi)),
      ihg (fun i hi => h i (List.mem_append_right _ hi))]
  | or f g ihf ihg =>
    simp only [sat_or, ihf (fun i hi => h i (List.mem_append_left _ hi)),
      ihg (fun i hi => h i (List.mem_append_right _ hi))]
  | true => rfl
  | false => rfl

section Checker

variable [DecidableEq α]

/-- Boolean checker for atom satisfaction. Regular membership uses
`EncodedRegex.memB`. -/
def satAtomB (σ : V → List α) : Atom α V → Bool
  | .eq t₁ t₂ => decide (eval σ t₁ = eval σ t₂)
  | .mem t e => e.memB (eval σ t)
  | .lenLe t k => decide ((eval σ t).length ≤ k)
  | .lenGe t k => decide (k ≤ (eval σ t).length)

/-- The Boolean checker is correct. -/
theorem satAtomB_iff {σ : V → List α} {a : Atom α V} :
    satAtomB σ a = true ↔ SatAtom σ a := by
  cases a with
  | eq t₁ t₂ => simp [satAtomB, SatAtom]
  | mem t e => simp [satAtomB, SatAtom, EncodedRegex.memB_iff]
  | lenLe t k => simp [satAtomB, SatAtom]
  | lenGe t k => simp [satAtomB, SatAtom]

/-- Boolean checker for formula satisfaction. -/
def satB (σ : V → List α) : Formula α V → Bool
  | .atom a => satAtomB σ a
  | .and f g => satB σ f && satB σ g
  | .or f g => satB σ f || satB σ g
  | .true => true
  | .false => false

/-- The Boolean checker is correct. -/
theorem satB_iff {σ : V → List α} {φ : Formula α V} :
    satB σ φ = true ↔ Sat σ φ := by
  induction φ with
  | atom a => simp [satB, satAtomB_iff]
  | and f g ihf ihg => simp [satB, ihf, ihg]
  | or f g ihf ihg => simp [satB, ihf, ihg]
  | true => simp [satB, Sat]
  | false => simp [satB, Sat]

end Checker

end Cslib.AutomatedReasoning.StringConstraints
