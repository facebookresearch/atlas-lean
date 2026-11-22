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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeCompleteness

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeCompletenessTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

variable {Γ Δ : List (Ty Unit)}

abbrev idBody : Tm [Atom] Atom := .var .zero

abbrev idTm : Tm [] (Atom ⇒ Atom) := .lam idBody

/-- Declarative beta conversion is complete for the computed observation. -/
example (a : Tm [] Atom) :
    NbeEq (.app idTm a) a := by
  apply BetaEtaEq.nbeEq
  exact .beta idBody a

/-- Eta conversion is also observed by normalization. -/
example (f : Tm Γ (Atom ⇒ Atom)) :
    NbeEq (.lam (.app (Tm.weaken f) (.var .zero))) f :=
  BetaEtaEq.nbeEq (.eta f)

/-- Compatible multi-step contraction preserves the term-level canonical
representative. -/
example {t u : Tm Γ Atom} (h : BetaEtaSteps t u) :
    normalizeTm t = normalizeTm u :=
  h.normalizeTm_eq

/-- A common reduct gives equal computed normal forms. -/
example {t u v : Tm Γ Atom} (ht : BetaEtaSteps t v)
    (hu : BetaEtaSteps u v) : NbeEq t u :=
  (show BetaEtaJoin t u from ⟨v, ht, hu⟩).nbeEq

/-- Pointwise conversion between substitutions is observed after substituting
into any term. -/
example (t : Tm Γ Atom) {σ τ : Sub Γ Δ} (h : SubBetaEtaEq σ τ) :
    NbeEq (Tm.subst σ t) (Tm.subst τ t) :=
  h.subst_nbeEq t

/-- Distinct computed representatives rule out declarative conversion. -/
example {t u : Tm Γ Atom} (h : normalizeTm t ≠ normalizeTm u) :
    ¬ BetaEtaEq t u :=
  not_betaEtaEq_of_normalizeTm_ne h

/-- Beta is literal equality in the beta-eta quotient. -/
example (body : BetaEtaClass Unit (Atom :: Γ) Atom)
    (a : BetaEtaClass Unit Γ Atom) :
    BetaEtaClass.app (BetaEtaClass.lam body) a =
      BetaEtaClass.instantiate body a :=
  BetaEtaClass.beta body a

/-- Eta is literal equality for an arbitrary quotient class, without choosing
a representative. -/
example (f : BetaEtaClass Unit Γ (Atom ⇒ Atom)) :
    BetaEtaClass.lam
        (BetaEtaClass.app (BetaEtaClass.rename .succ f)
          (BetaEtaClass.ofTm (.var .zero))) = f :=
  BetaEtaClass.eta f

/-- Quotient operations respect renaming composition. -/
example (ρ : Ren Γ Δ) (σ : Ren Δ Γ) (q : BetaEtaClass Unit Γ Atom) :
    BetaEtaClass.rename σ (BetaEtaClass.rename ρ q) =
      BetaEtaClass.rename (Var.comp ρ σ) q :=
  BetaEtaClass.rename_comp ρ σ q

/-- Renaming distributes over quotient application. -/
example (ρ : Ren Γ Δ) (f : BetaEtaClass Unit Γ (Atom ⇒ Atom))
    (a : BetaEtaClass Unit Γ Atom) :
    BetaEtaClass.rename ρ (BetaEtaClass.app f a) =
      BetaEtaClass.app (BetaEtaClass.rename ρ f)
        (BetaEtaClass.rename ρ a) :=
  BetaEtaClass.rename_app ρ f a

/-- The quotient interpretation validates application compositionally. -/
example (I : Unit → Type) (η : Env I Γ)
    (f : BetaEtaClass Unit Γ (Atom ⇒ Atom))
    (a : BetaEtaClass Unit Γ Atom) :
    BetaEtaClass.denote I η (BetaEtaClass.app f a) =
      BetaEtaClass.denote I η f (BetaEtaClass.denote I η a) :=
  BetaEtaClass.denote_app I η f a

/-- The quotient interpretation validates lambda abstraction
compositionally. -/
example (I : Unit → Type) (η : Env I Γ)
    (body : BetaEtaClass Unit (Atom :: Γ) Atom) :
    BetaEtaClass.denote I η (BetaEtaClass.lam body) =
      fun a => BetaEtaClass.denote I (Env.cons a η) body :=
  BetaEtaClass.denote_lam I η body

/-- Observational classes are classified exactly by eta-long normal forms. -/
example (q r : NbeClass Unit Γ Atom) :
    q = r ↔ NbeClass.normalForm q = NbeClass.normalForm r :=
  NbeClass.eq_iff_normalForm_eq

/-- Every observational class has a canonical normal-form representative. -/
example (q : NbeClass Unit Γ Atom) :
    q = NbeClass.ofNf (NbeClass.normalForm q) :=
  NbeClass.eq_ofNf_normalForm q

/-- Passing from declarative classes to observational classes preserves the
normal-form observation. -/
example (q : BetaEtaClass Unit Γ Atom) :
    NbeClass.normalForm (betaEtaToNbe q) = BetaEtaClass.normalForm q :=
  normalForm_betaEtaToNbe q

/-- Completeness can equivalently be stated as convertibility to the computed
canonical representative. -/
example :
    BetaEtaComplete Unit Γ Atom ↔
      ∀ t : Tm Γ Atom, BetaEtaEq t (normalizeTm t) :=
  betaEtaComplete_iff_normalize Unit Γ Atom

/-- Completeness is exactly injectivity of the canonical quotient map. -/
example :
    BetaEtaComplete Unit Γ Atom ↔
      Function.Injective
        (betaEtaToNbe (Base := Unit) (Γ := Γ) (A := Atom)) :=
  betaEtaComplete_iff_injective

#print axioms BetaEtaEq.nbeEval_related
#print axioms BetaEtaEq.nbeEq
#print axioms BetaEtaClass.beta
#print axioms BetaEtaClass.denote
#print axioms NbeClass.equivNormalForm
#print axioms betaEtaComplete_iff_injective

end Cslib.Languages.LambdaCalculus.Stlc.NbeCompletenessTests
