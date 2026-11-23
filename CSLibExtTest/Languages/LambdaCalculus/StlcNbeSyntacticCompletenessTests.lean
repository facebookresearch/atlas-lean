/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeDecisionLaws

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeSyntacticCompletenessTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

variable {Γ Δ : List (Ty Unit)}

abbrev idBody : Tm [Atom] Atom := .var .zero
abbrev idTm : Tm [] (Atom ⇒ Atom) := .lam idBody

/-- Every term is convertible to its computed canonical representative. -/
example (t : Tm Γ Atom) : BetaEtaEq t (normalizeTm t) :=
  betaEtaEq_normalizeTm t

/-- Equality of normal forms is now sufficient for conversion. -/
example {t u : Tm Γ Atom} (h : normalizeTm t = normalizeTm u) :
    BetaEtaEq t u := betaEtaEq_of_normalizeTm_eq h

/-- Declarative conversion and NbE equality coincide. -/
example (t u : Tm Γ Atom) : BetaEtaEq t u ↔ NbeEq t u :=
  BetaEtaEq.iff_nbeEq

/-- The global completeness predicate is discharged. -/
example : BetaEtaComplete Unit Γ Atom := betaEtaComplete

/-- Canonical convertible terms are literally equal. -/
example {t u : Tm Γ Atom} (ht : IsCanonical t) (hu : IsCanonical u)
    (h : BetaEtaEq t u) : t = u :=
  BetaEtaEq.eq_of_isCanonical ht hu h

/-- Eta-long normal forms have unique beta-eta classes. -/
example (n m : Nf Γ Atom) :
    BetaEtaEq n.toTm m.toTm ↔ n = m := BetaEtaEq.nf_toTm_iff_eq

/-- The beta redex and its contractum compare equal computationally. -/
example (a : Tm [] Atom) :
    betaEtaEquivalent (.app idTm a) a = true := by
  exact betaEtaEquivalent_beta idBody a

/-- Eta expansion also compares equal computationally. -/
example (f : Tm Γ (Atom ⇒ Atom)) :
    betaEtaEquivalent
      (.lam (.app (Tm.weaken f) (.var .zero))) f = true :=
  betaEtaEquivalent_eta f

/-! The following closed computations exercise both outcomes on inhabited
open syntax rather than merely invoking the propositional characterizations. -/

abbrev leftVar : Tm [Atom, Atom] Atom := .var .zero
abbrev rightVar : Tm [Atom, Atom] Atom := .var (.succ .zero)

/-- Comparing an open variable with itself computes to true. -/
example : betaEtaEquivalent leftVar leftVar = true := by decide

/-- Distinct open variables compute to distinct normal forms. -/
example : betaEtaEquivalent leftVar rightVar = false := by decide

/-- Quotient comparison computes positively on equal representatives. -/
example : BetaEtaClass.equivalent
    (BetaEtaClass.ofTm leftVar) (BetaEtaClass.ofTm leftVar) = true := by
  decide

/-- Quotient comparison computes negatively on distinct representatives. -/
example : BetaEtaClass.equivalent
    (BetaEtaClass.ofTm leftVar) (BetaEtaClass.ofTm rightVar) = false := by
  decide

/-- The boolean comparison is compositional for application. -/
example {f g : Tm Γ (Atom ⇒ Atom)} {a b : Tm Γ Atom}
    (hf : betaEtaEquivalent f g = true)
    (ha : betaEtaEquivalent a b = true) :
    betaEtaEquivalent (.app f a) (.app g b) = true :=
  betaEtaEquivalent_app hf ha

/-- The boolean comparison is compositional for abstraction. -/
example {t u : Tm (Atom :: Γ) Atom}
    (h : betaEtaEquivalent t u = true) :
    betaEtaEquivalent (.lam t) (.lam u) = true :=
  betaEtaEquivalent_lam h

/-- Pointwise equivalent substitutions act equivalently. -/
example (t : Tm Γ Atom) {σ τ : Sub Γ Δ}
    (h : ∀ {B} (x : Var Γ B), betaEtaEquivalent (σ x) (τ x) = true) :
    betaEtaEquivalent (Tm.subst σ t) (Tm.subst τ t) = true :=
  betaEtaEquivalent_subst_pointwise t h

/-- Declarative and observational quotient classes are equivalent. -/
noncomputable example : BetaEtaClass Unit Γ Atom ≃ NbeClass Unit Γ Atom :=
  betaEtaEquivNbeClass

/-- Declarative quotient classes are classified by normal forms. -/
noncomputable example : BetaEtaClass Unit Γ Atom ≃ Nf Γ Atom := betaEtaEquivNf

/-- The normal-form embedding is a bijection. -/
example : Function.Bijective
    (fun n : Nf Γ Atom => BetaEtaClass.ofTm n.toTm) :=
  betaEtaNormalForm_bijective

/-- Quotient comparison agrees with term comparison on representatives. -/
example (t u : Tm Γ Atom) :
    BetaEtaClass.equivalent (BetaEtaClass.ofTm t) (BetaEtaClass.ofTm u) =
      betaEtaEquivalent t u :=
  BetaEtaClass.equivalent_ofTm t u

/-- Equality of beta-eta quotient classes is decidable. -/
example (q r : BetaEtaClass Unit Γ Atom) : Decidable (q = r) := inferInstance

/-- Equality of observational quotient classes is decidable. -/
example (q r : NbeClass Unit Γ Atom) : Decidable (q = r) := inferInstance

#print axioms quote_syntactic
#print axioms reflect_syntactic
#print axioms nbeEval_syntactic
#print axioms betaEtaEq_normalizeTm
#print axioms betaEtaEq_of_normalizeTm_eq
#print axioms betaEtaEquivNbeClass
#print axioms betaEtaEquivalent_eq_true

end Cslib.Languages.LambdaCalculus.Stlc.NbeSyntacticCompletenessTests
