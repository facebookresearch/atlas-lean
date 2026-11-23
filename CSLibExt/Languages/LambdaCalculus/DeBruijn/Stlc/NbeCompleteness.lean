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

/-
# Completeness of STLC normalization by evaluation for beta-eta conversion
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeConversion
public import Mathlib.Logic.Equiv.Defs

/-!
# Completeness of STLC normalization by evaluation

This file proves that beta-eta conversion is observed by the logical Kripke
semantics used by normalization by evaluation.  Reification therefore maps
convertible terms to the same eta-long normal form.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Θ Ω : List (Ty Base)}

namespace SemEnv

/-- Evaluating a singleton syntactic substitution extends any semantic
environment by the interpretation of its distinguished image. -/
theorem evalSub_single (a : Tm Γ A) (η : SemEnv Δ Γ) :
    @evalSub Base (A :: Γ) Γ Δ (Sub.single a) η =
      @cons Base A Γ Δ (nbeEval a η) η := by
  funext B x
  cases x with
  | zero => rfl
  | succ x => rfl

end SemEnv

namespace BetaEtaEq

/-- Beta-eta conversion relates the NbE interpretations of its endpoints in
every pair of logically related semantic environments. -/
theorem nbeEval_related {t u : Tm Γ A} (h : BetaEtaEq t u)
    (ξ ζ : SemEnv Δ Γ) (hξ : ξ.Logical) (hζ : ζ.Logical)
    (hξζ : ξ.Related ζ) :
    Sem.Related A (nbeEval t ξ) (nbeEval u ζ) := by
  induction h generalizing Δ with
  | refl t => exact nbeEval_logically_related t ξ ζ hξ hζ hξζ
  | symm h ih =>
      exact Sem.Related.symm _
        (ih ζ ξ hζ hξ (fun x => Sem.Related.symm _ (hξζ x)))
  | trans h₁ h₂ ih₁ ih₂ =>
      exact Sem.Related.trans _
        (nbeEval_logical _ ξ hξ) (nbeEval_logical _ ζ hζ)
        (nbeEval_logical _ ζ hζ)
        (ih₁ ξ ζ hξ hζ hξζ)
        (ih₂ ζ ζ hζ hζ hζ.related_refl)
  | @app Γ A B f g a b hf ha ihf iha =>
      exact (ihf ξ ζ hξ hζ hξζ) Var.id _ _
        (nbeEval_logical a ξ hξ) (nbeEval_logical b ζ hζ)
        (iha ξ ζ hξ hζ hξζ)
  | @lam Γ A B body body' h ih =>
      intro Θ ρ a b ha hb hab
      simp only [nbeEval_lam_apply]
      exact ih (SemEnv.cons a (SemEnv.rename ρ ξ))
        (SemEnv.cons b (SemEnv.rename ρ ζ))
        (SemEnv.Logical.cons ha (hξ.rename ρ))
        (SemEnv.Logical.cons hb (hζ.rename ρ))
        (SemEnv.Related.cons hab (hξζ.rename ρ))
  | @beta Γ A B body a =>
      simp only [nbeEval_app, nbeEval_lam_apply]
      have ha : Sem.Related A (nbeEval a ξ) (nbeEval a ζ) :=
        nbeEval_logically_related a ξ ζ hξ hζ hξζ
      have henv :
          SemEnv.Related
            (SemEnv.cons (nbeEval a ξ) (SemEnv.rename Var.id ξ))
            (SemEnv.evalSub (Sub.single a) ζ) := by
        rw [SemEnv.evalSub_single]
        rw [SemEnv.rename_id]
        exact SemEnv.Related.cons ha hξζ
      have hbody := nbeEval_logically_related body _ _
        (SemEnv.Logical.cons (nbeEval_logical a ξ hξ) (hξ.rename Var.id))
        (hζ.evalSub (Sub.single a)) henv
      exact Sem.Related.trans B
        (nbeEval_logical _ _
          (SemEnv.Logical.cons (nbeEval_logical a ξ hξ) (hξ.rename Var.id)))
        (nbeEval_logical _ _ (hζ.evalSub (Sub.single a)))
        (nbeEval_logical _ ζ hζ) hbody
        (Sem.Related.symm B
          (nbeEval_subst_related body (Sub.single a) ζ hζ))
  | @eta Γ A B f =>
      intro Θ ρ a b ha hb hab
      simp only [nbeEval_lam_apply, nbeEval_app, nbeEval_var,
        SemEnv.cons_zero]
      rw [Tm.weaken, nbeEval_rename_source]
      have henv :
          @SemEnv.compRen Base Γ (A :: Γ) Θ
              (SemEnv.cons a (SemEnv.rename ρ ξ))
              (.succ : Ren Γ (A :: Γ)) =
            @SemEnv.rename Base Γ Δ Θ ρ ξ := by
        funext C x
        rfl
      rw [henv]
      rw [← nbeEval_rename_sem f ξ hξ.natural ρ]
      simp only [Sem.rename_arr_apply]
      have hcomp :
          @Var.comp Base Δ Θ Θ (ρ : Ren Δ Θ) (Var.id : Ren Θ Θ) =
            (ρ : Ren Δ Θ) := by
        funext C x
        rfl
      rw [hcomp]
      exact (nbeEval_logically_related f ξ ζ hξ hζ hξζ) ρ a b ha hb hab

/-- Beta-eta-convertible terms have identical eta-long normal forms. -/
theorem nbeEq {t u : Tm Γ A} (h : BetaEtaEq t u) : NbeEq t u := by
  unfold NbeEq normalizeNf
  apply quote_eq_of_related A
  exact h.nbeEval_related SemEnv.identity SemEnv.identity
    SemEnv.logical_identity SemEnv.logical_identity
    SemEnv.logical_identity.related_refl

/-- Beta-eta conversion preserves the term-level canonical representative. -/
theorem normalizeTm_eq {t u : Tm Γ A} (h : BetaEtaEq t u) :
    normalizeTm t = normalizeTm u :=
  NbeEq.iff_normalizeTm_eq.mp h.nbeEq

end BetaEtaEq

/-! ## Consequences for the operational presentations -/

namespace BetaEtaStep

/-- One compatible contraction preserves the computed normal form. -/
theorem nbeEq {t u : Tm Γ A} (h : BetaEtaStep t u) : NbeEq t u :=
  h.betaEtaEq.nbeEq

/-- One compatible contraction preserves the erased canonical
representative. -/
theorem normalizeTm_eq {t u : Tm Γ A} (h : BetaEtaStep t u) :
    normalizeTm t = normalizeTm u :=
  h.betaEtaEq.normalizeTm_eq

end BetaEtaStep

namespace BetaEtaSteps

/-- Every finite directed contraction sequence preserves the computed normal
form. -/
theorem nbeEq {t u : Tm Γ A} (h : BetaEtaSteps t u) : NbeEq t u :=
  h.betaEtaEq.nbeEq

/-- A finite contraction sequence preserves the erased canonical
representative. -/
theorem normalizeTm_eq {t u : Tm Γ A} (h : BetaEtaSteps t u) :
    normalizeTm t = normalizeTm u :=
  NbeEq.iff_normalizeTm_eq.mp h.nbeEq

end BetaEtaSteps

namespace BetaEtaJoin

/-- Terms with a common reduct have identical computed normal forms. -/
theorem nbeEq {t u : Tm Γ A} (h : BetaEtaJoin t u) : NbeEq t u :=
  h.betaEtaEq.nbeEq

/-- Joinable terms have the same erased canonical representative. -/
theorem normalizeTm_eq {t u : Tm Γ A} (h : BetaEtaJoin t u) :
    normalizeTm t = normalizeTm u :=
  NbeEq.iff_normalizeTm_eq.mp h.nbeEq

end BetaEtaJoin

namespace BetaEtaZigzag

/-- Every finite conversion zigzag preserves the computed normal form. -/
theorem nbeEq {t u : Tm Γ A} (h : BetaEtaZigzag t u) : NbeEq t u :=
  h.betaEtaEq.nbeEq

/-- A conversion zigzag preserves the erased canonical representative. -/
theorem normalizeTm_eq {t u : Tm Γ A} (h : BetaEtaZigzag t u) :
    normalizeTm t = normalizeTm u :=
  NbeEq.iff_normalizeTm_eq.mp h.nbeEq

end BetaEtaZigzag

namespace SubBetaEtaEq

/-- Pointwise beta-eta conversion of substitutions makes their instances of
every term compute to the same normal form. -/
theorem subst_nbeEq (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : SubBetaEtaEq σ τ) : NbeEq (Tm.subst σ t) (Tm.subst τ t) :=
  (BetaEtaEq.subst_pointwise t h).nbeEq

/-- Pointwise-convertible substitutions give equal canonical
representatives after substitution. -/
theorem normalizeTm_subst_eq (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : SubBetaEtaEq σ τ) :
    normalizeTm (Tm.subst σ t) = normalizeTm (Tm.subst τ t) :=
  NbeEq.iff_normalizeTm_eq.mp (h.subst_nbeEq t)

end SubBetaEtaEq

namespace SubBetaEtaZigzag

/-- Pointwise zigzags of substitution images preserve normalization after
substitution into any term. -/
theorem subst_nbeEq (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : SubBetaEtaZigzag σ τ) : NbeEq (Tm.subst σ t) (Tm.subst τ t) :=
  SubBetaEtaEq.subst_nbeEq t h.subBetaEtaEq

end SubBetaEtaZigzag

/-! ## Canonical uniqueness and refutation principles -/

/-- A canonical term beta-eta-convertible to a source is its computed
canonical representative. -/
theorem canonical_eq_normalizeTm_of_betaEtaEq {t c : Tm Γ A}
    (hc : IsCanonical c) (h : BetaEtaEq t c) : c = normalizeTm t :=
  NbeEq.canonical_unique t c hc h.nbeEq

/-- Beta-eta-convertible canonical terms are syntactically identical. -/
theorem eq_of_canonical_betaEtaEq {t u : Tm Γ A}
    (ht : IsCanonical t) (hu : IsCanonical u) (h : BetaEtaEq t u) : t = u :=
  NbeEq.eq_of_isCanonical ht hu h.nbeEq

/-- Distinct computed normal forms refute beta-eta convertibility. -/
theorem not_betaEtaEq_of_normalizeNf_ne {t u : Tm Γ A}
    (h : normalizeNf t ≠ normalizeNf u) : ¬ BetaEtaEq t u :=
  fun htu => h htu.nbeEq

/-- Distinct erased canonical representatives refute beta-eta
convertibility. -/
theorem not_betaEtaEq_of_normalizeTm_ne {t u : Tm Γ A}
    (h : normalizeTm t ≠ normalizeTm u) : ¬ BetaEtaEq t u :=
  fun htu => h htu.normalizeTm_eq

/-! ## Quotients of the equational and observational theories -/

/-- The setoid generated by declarative beta-eta conversion at one intrinsic
context and type. -/
def betaEtaSetoid (Base : Type u) (Γ : List (Ty Base)) (A : Ty Base) :
    Setoid (Tm Γ A) where
  r := BetaEtaEq
  iseqv := BetaEtaEq.equivalence

/-- Terms modulo declarative beta-eta conversion. -/
abbrev BetaEtaClass (Base : Type u) (Γ : List (Ty Base)) (A : Ty Base) :=
  Quotient (betaEtaSetoid Base Γ A)

namespace BetaEtaClass

/-- Embed a term in the beta-eta quotient. -/
def ofTm (t : Tm Γ A) : BetaEtaClass Base Γ A :=
  Quotient.mk (betaEtaSetoid Base Γ A) t

/-- Declaratively convertible terms determine the same beta-eta class. -/
theorem sound {t u : Tm Γ A} (h : BetaEtaEq t u) :
    ofTm t = ofTm u :=
  Quotient.sound h

/-- Equality of beta-eta classes represented by terms recovers a conversion
derivation. -/
theorem exact {t u : Tm Γ A} (h : ofTm t = ofTm u) : BetaEtaEq t u :=
  Quotient.exact h

/-- Renaming descends to beta-eta classes. -/
def rename (ρ : Ren Γ Δ) : BetaEtaClass Base Γ A → BetaEtaClass Base Δ A :=
  Quotient.lift
    (fun t => ofTm (Tm.rename ρ t))
    (fun _ _ h => Quotient.sound (h.rename ρ))

@[simp]
theorem rename_ofTm (ρ : Ren Γ Δ) (t : Tm Γ A) :
    rename ρ (ofTm t) = ofTm (Tm.rename ρ t) := rfl

/-- Substitution by a fixed syntactic substitution descends to beta-eta
classes. -/
def subst (σ : Sub Γ Δ) : BetaEtaClass Base Γ A → BetaEtaClass Base Δ A :=
  Quotient.lift
    (fun t => ofTm (Tm.subst σ t))
    (fun _ _ h => Quotient.sound (h.subst σ))

@[simp]
theorem subst_ofTm (σ : Sub Γ Δ) (t : Tm Γ A) :
    subst σ (ofTm t) = ofTm (Tm.subst σ t) := rfl

/-- Application is well defined on beta-eta classes. -/
def app : BetaEtaClass Base Γ (A ⇒ B) → BetaEtaClass Base Γ A →
    BetaEtaClass Base Γ B :=
  Quotient.lift
    (fun f => Quotient.lift
      (fun a => ofTm (.app f a))
      (fun _ _ ha => Quotient.sound (.app (.refl _) ha)))
    (fun _ _ hf => funext fun q => Quotient.inductionOn q fun _a =>
      Quotient.sound (.app hf (.refl _)))

@[simp]
theorem app_ofTm (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    app (ofTm f) (ofTm a) = ofTm (.app f a) := rfl

/-- Lambda abstraction is well defined on beta-eta classes. -/
def lam : BetaEtaClass Base (A :: Γ) B → BetaEtaClass Base Γ (A ⇒ B) :=
  Quotient.lift
    (fun body => ofTm (.lam body))
    (fun _ _ h => Quotient.sound (.lam h))

@[simp]
theorem lam_ofTm (body : Tm (A :: Γ) B) :
    lam (ofTm body) = ofTm (.lam body) := rfl

/-- Instantiation is well defined in both a body class and an argument
class. -/
def instantiate : BetaEtaClass Base (A :: Γ) B → BetaEtaClass Base Γ A →
    BetaEtaClass Base Γ B :=
  Quotient.lift
    (fun body => Quotient.lift
      (fun a => ofTm (Tm.instantiate body a))
      (fun _ _ ha => Quotient.sound ((BetaEtaEq.refl _).instantiate_congr ha)))
    (fun _ _ hbody => funext fun q => Quotient.inductionOn q fun _a =>
      Quotient.sound (hbody.instantiate_congr (.refl _)))

@[simp]
theorem instantiate_ofTm (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    instantiate (ofTm body) (ofTm a) = ofTm (Tm.instantiate body a) := rfl

/-- The beta law holds as literal equality in the beta-eta quotient. -/
theorem beta (body : BetaEtaClass Base (A :: Γ) B)
    (a : BetaEtaClass Base Γ A) :
    app (lam body) a = instantiate body a := by
  induction body using Quotient.inductionOn with
  | _ body =>
    induction a using Quotient.inductionOn with
    | _ a => exact sound (.beta body a)

/-- The eta law holds as literal equality for every beta-eta quotient
class. -/
theorem eta (f : BetaEtaClass Base Γ (A ⇒ B)) :
    lam (app (rename .succ f) (ofTm (.var .zero))) = f := by
  induction f using Quotient.inductionOn with
  | _ f => exact sound (.eta f)

/-- The representative-level eta equation is a direct instance of the
quotient eta law. -/
theorem eta_ofTm (f : Tm Γ (A ⇒ B)) :
    lam (ofTm (.app (Tm.weaken f) (.var .zero))) = ofTm f :=
  eta (ofTm f)

/-- The computed eta-long normal form is well defined on beta-eta classes. -/
def normalForm : BetaEtaClass Base Γ A → Nf Γ A :=
  Quotient.lift normalizeNf (fun _ _ h => h.nbeEq)

@[simp]
theorem normalForm_ofTm (t : Tm Γ A) :
    normalForm (ofTm t) = normalizeNf t := rfl

/-- Renaming beta-eta classes obeys the identity law. -/
theorem rename_id (q : BetaEtaClass Base Γ A) : rename Var.id q = q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (BetaEtaEq.of_eq (Tm.rename_id t))

/-- Successive renamings act by their composite on the quotient. -/
theorem rename_comp (ρ : Ren Γ Δ) (σ : Ren Δ Θ)
    (q : BetaEtaClass Base Γ A) :
    rename σ (rename ρ q) = rename (Var.comp ρ σ) q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (BetaEtaEq.of_eq (Tm.rename_comp ρ σ t))

/-- Substitution by the identity substitution is the identity action. -/
theorem subst_id (q : BetaEtaClass Base Γ A) : subst Sub.id q = q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (BetaEtaEq.of_eq (Tm.subst_id t))

/-- Successive substitutions act by substitution composition on the
quotient. -/
theorem subst_comp (σ : Sub Γ Δ) (τ : Sub Δ Θ)
    (q : BetaEtaClass Base Γ A) :
    subst τ (subst σ q) = subst (Sub.comp σ τ) q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (BetaEtaEq.of_eq (Tm.subst_subst σ τ t))

/-! ### Structural laws on beta-eta classes -/

/-- Pointwise equal renamings induce equal actions on beta-eta classes. -/
theorem rename_congr {ρ σ : Ren Γ Δ}
    (h : ∀ {C} (x : Var Γ C), ρ x = σ x)
    (q : BetaEtaClass Base Γ A) : rename ρ q = rename σ q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (.of_eq (Tm.rename_congr h t))

/-- Pointwise equal substitutions induce equal actions on beta-eta classes. -/
theorem subst_congr {σ τ : Sub Γ Δ}
    (h : ∀ {C} (x : Var Γ C), σ x = τ x)
    (q : BetaEtaClass Base Γ A) : subst σ q = subst τ q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (.of_eq (Tm.subst_congr h t))

/-- Renaming distributes over quotient application. -/
theorem rename_app (ρ : Ren Γ Δ) (f : BetaEtaClass Base Γ (A ⇒ B))
    (a : BetaEtaClass Base Γ A) :
    rename ρ (app f a) = app (rename ρ f) (rename ρ a) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction a using Quotient.inductionOn with
    | _ a => rfl

/-- Renaming distributes over quotient lambda abstraction. -/
theorem rename_lam (ρ : Ren Γ Δ) (body : BetaEtaClass Base (A :: Γ) B) :
    rename ρ (lam body) = lam (rename (Var.lift ρ) body) := by
  induction body using Quotient.inductionOn with
  | _ body => rfl

/-- Substitution distributes over quotient application. -/
theorem subst_app (σ : Sub Γ Δ) (f : BetaEtaClass Base Γ (A ⇒ B))
    (a : BetaEtaClass Base Γ A) :
    subst σ (app f a) = app (subst σ f) (subst σ a) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction a using Quotient.inductionOn with
    | _ a => rfl

/-- Substitution distributes over quotient lambda abstraction. -/
theorem subst_lam (σ : Sub Γ Δ) (body : BetaEtaClass Base (A :: Γ) B) :
    subst σ (lam body) = lam (subst (Sub.lift σ) body) := by
  induction body using Quotient.inductionOn with
  | _ body => rfl

/-- Weakening of a quotient class is renaming by successor. -/
def weaken (q : BetaEtaClass Base Γ A) : BetaEtaClass Base (B :: Γ) A :=
  rename .succ q

@[simp]
theorem weaken_ofTm (t : Tm Γ A) :
    weaken (B := B) (ofTm t) = ofTm (Tm.weaken t) := rfl

/-- Weakening distributes over quotient application. -/
theorem weaken_app (f : BetaEtaClass Base Γ (A ⇒ B))
    (a : BetaEtaClass Base Γ A) :
    weaken (B := C) (app f a) =
      app (weaken (B := C) f) (weaken (B := C) a) :=
  rename_app .succ f a

/-- Renaming after substitution fuses into a single substitution. -/
theorem subst_rename (ρ : Ren Γ Δ) (σ : Sub Δ Θ)
    (q : BetaEtaClass Base Γ A) :
    subst σ (rename ρ q) = subst (fun x => σ (ρ x)) q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (.of_eq (Tm.subst_rename σ ρ t))

/-- Substitution followed by renaming fuses into a single substitution. -/
theorem rename_subst (σ : Sub Γ Δ) (ρ : Ren Δ Θ)
    (q : BetaEtaClass Base Γ A) :
    rename ρ (subst σ q) = subst (fun x => Tm.rename ρ (σ x)) q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (.of_eq (Tm.rename_subst ρ σ t))

/-- The normal-form observation of a renamed class is the renamed normal
form. -/
theorem normalForm_rename (ρ : Ren Γ Δ) (q : BetaEtaClass Base Γ A) :
    normalForm (rename ρ q) = (normalForm q).rename ρ := by
  induction q using Quotient.inductionOn with
  | _ t => exact normalizeNf_rename t ρ

/-- Equality in the beta-eta quotient implies equality of normal-form
observations. -/
theorem normalForm_congr {q r : BetaEtaClass Base Γ A} (h : q = r) :
    normalForm q = normalForm r := congrArg normalForm h

/-- The beta equation is preserved by every further renaming. -/
theorem rename_beta (ρ : Ren Γ Δ)
    (body : BetaEtaClass Base (A :: Γ) B) (a : BetaEtaClass Base Γ A) :
    rename ρ (app (lam body) a) = rename ρ (instantiate body a) :=
  congrArg (rename ρ) (beta body a)

/-- The eta equation is preserved by every further substitution. -/
theorem subst_eta (σ : Sub Γ Δ) (f : BetaEtaClass Base Γ (A ⇒ B)) :
    subst σ (lam (app (rename .succ f) (ofTm (.var .zero)))) =
      subst σ f :=
  congrArg (subst σ) (eta f)

end BetaEtaClass

/-- The NbE observational setoid identifies terms with equal computed normal
forms. -/
def nbeSetoid (Base : Type u) (Γ : List (Ty Base)) (A : Ty Base) :
    Setoid (Tm Γ A) where
  r := NbeEq
  iseqv := nbeEq_equivalence

/-- Terms modulo equality of their computed eta-long normal forms. -/
abbrev NbeClass (Base : Type u) (Γ : List (Ty Base)) (A : Ty Base) :=
  Quotient (nbeSetoid Base Γ A)

namespace NbeClass

/-- Embed a term in its NbE observational quotient. -/
def ofTm (t : Tm Γ A) : NbeClass Base Γ A :=
  Quotient.mk (nbeSetoid Base Γ A) t

/-- NbE-equivalent terms determine the same observational class. -/
theorem sound {t u : Tm Γ A} (h : NbeEq t u) : ofTm t = ofTm u :=
  Quotient.sound h

/-- Equality of represented observational classes recovers equality of
computed normal forms. -/
theorem exact {t u : Tm Γ A} (h : ofTm t = ofTm u) : NbeEq t u :=
  Quotient.exact h

/-- Read the canonical normal form represented by an observational class. -/
def normalForm : NbeClass Base Γ A → Nf Γ A :=
  Quotient.lift normalizeNf (fun _ _ h => h)

/-- Embed an eta-long normal form as an observational class. -/
def ofNf (n : Nf Γ A) : NbeClass Base Γ A := ofTm n.toTm

@[simp]
theorem normalForm_ofTm (t : Tm Γ A) : normalForm (ofTm t) = normalizeNf t := rfl

@[simp]
theorem normalForm_ofNf (n : Nf Γ A) : normalForm (ofNf n) = n :=
  normalizeNf_toTm n

/-- NbE observational classes are exactly eta-long normal forms. -/
def equivNormalForm : Equiv (NbeClass Base Γ A) (Nf Γ A) where
  toFun := normalForm
  invFun := ofNf
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ t =>
      exact sound (NbeEq.normalize_right t).symm
  right_inv := normalForm_ofNf

/-- Renaming descends to observational classes because NbE equality is
natural in the source context. -/
def rename (ρ : Ren Γ Δ) : NbeClass Base Γ A → NbeClass Base Δ A :=
  Quotient.lift
    (fun t => ofTm (Tm.rename ρ t))
    (fun _ _ h => Quotient.sound (h.rename ρ))

@[simp]
theorem rename_ofTm (ρ : Ren Γ Δ) (t : Tm Γ A) :
    rename ρ (ofTm t) = ofTm (Tm.rename ρ t) := rfl

/-- Renaming observational classes obeys the identity law. -/
theorem rename_id (q : NbeClass Base Γ A) : rename Var.id q = q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (.of_eq (Tm.rename_id t))

/-- Successive renamings of observational classes compose. -/
theorem rename_comp (ρ : Ren Γ Δ) (σ : Ren Δ Θ)
    (q : NbeClass Base Γ A) :
    rename σ (rename ρ q) = rename (Var.comp ρ σ) q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (.of_eq (Tm.rename_comp ρ σ t))

/-- Pointwise equal renamings induce equal actions on observational
classes. -/
theorem rename_congr {ρ σ : Ren Γ Δ}
    (h : ∀ {C} (x : Var Γ C), ρ x = σ x)
    (q : NbeClass Base Γ A) : rename ρ q = rename σ q := by
  induction q using Quotient.inductionOn with
  | _ t => exact sound (.of_eq (Tm.rename_congr h t))

/-- The canonical observation of a renamed class is the renamed canonical
normal form. -/
theorem normalForm_rename (ρ : Ren Γ Δ) (q : NbeClass Base Γ A) :
    normalForm (rename ρ q) = (normalForm q).rename ρ := by
  induction q using Quotient.inductionOn with
  | _ t => exact normalizeNf_rename t ρ

end NbeClass

/-! ## Factoring beta-eta conversion through canonical forms -/

/-- The inclusion of beta-eta conversion in NbE equality induces a canonical
map between the two quotients. -/
def betaEtaToNbe : BetaEtaClass Base Γ A → NbeClass Base Γ A :=
  Quotient.lift NbeClass.ofTm (fun _ _ h => Quotient.sound h.nbeEq)

@[simp]
theorem betaEtaToNbe_ofTm (t : Tm Γ A) :
    betaEtaToNbe (BetaEtaClass.ofTm t) = NbeClass.ofTm t := rfl

/-- Every observational class has a beta-eta class representative. -/
theorem betaEtaToNbe_surjective :
    Function.Surjective (betaEtaToNbe (Base := Base) (Γ := Γ) (A := A)) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ t => exact ⟨BetaEtaClass.ofTm t, rfl⟩

/-- Computing a normal form before or after passing from the beta-eta quotient
to the observational quotient gives the same result. -/
theorem normalForm_betaEtaToNbe (q : BetaEtaClass Base Γ A) :
    NbeClass.normalForm (betaEtaToNbe q) = BetaEtaClass.normalForm q := by
  induction q using Quotient.inductionOn with
  | _ t => rfl

/-! ## Universal and semantic properties of the beta-eta quotient -/

namespace BetaEtaClass

universe v w

/-- Eliminate a beta-eta class into any type by supplying an operation that
is invariant under declarative conversion. -/
def lift {X : Sort v} (f : Tm Γ A → X)
    (hf : ∀ {t u}, BetaEtaEq t u → f t = f u) :
    BetaEtaClass Base Γ A → X :=
  Quotient.lift f (fun _ _ h => hf h)

@[simp]
theorem lift_ofTm {X : Sort v} (f : Tm Γ A → X)
    (hf : ∀ {t u}, BetaEtaEq t u → f t = f u) (t : Tm Γ A) :
    lift f hf (ofTm t) = f t := rfl

/-- Two maps out of the quotient are equal when they agree on every embedded
term. -/
theorem hom_ext {X : Sort v} {f g : BetaEtaClass Base Γ A → X}
    (h : ∀ t, f (ofTm t) = g (ofTm t)) : f = g := by
  funext q
  induction q using Quotient.inductionOn with
  | _ t => exact h t

/-- The quotient lift is the unique map extending its representative-level
operation. -/
theorem lift_unique {X : Sort v} (f : Tm Γ A → X)
    (hf : ∀ {t u}, BetaEtaEq t u → f t = f u)
    (g : BetaEtaClass Base Γ A → X)
    (hg : ∀ t, g (ofTm t) = f t) : g = lift f hf :=
  hom_ext fun t => (hg t).trans (lift_ofTm f hf t).symm

/-- Interpret a beta-eta class in an arbitrary set-theoretic model and
environment.  Soundness of declarative conversion makes interpretation
independent of the chosen representative. -/
def denote (I : Base → Type v) (η : Env I Γ) :
    BetaEtaClass Base Γ A → Ty.denote I A :=
  lift (fun t => Tm.denote I t η) (fun h => h.semEq I η)

@[simp]
theorem denote_ofTm (I : Base → Type v) (η : Env I Γ) (t : Tm Γ A) :
    denote I η (ofTm t) = Tm.denote I t η := rfl

/-- Quotient application is interpreted as semantic function application. -/
theorem denote_app (I : Base → Type v) (η : Env I Γ)
    (f : BetaEtaClass Base Γ (A ⇒ B)) (a : BetaEtaClass Base Γ A) :
    denote I η (app f a) = denote I η f (denote I η a) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction a using Quotient.inductionOn with
    | _ a => rfl

/-- Quotient lambda abstraction is interpreted as semantic abstraction. -/
theorem denote_lam (I : Base → Type v) (η : Env I Γ)
    (body : BetaEtaClass Base (A :: Γ) B) :
    denote I η (lam body) = fun a => denote I (Env.cons a η) body := by
  induction body using Quotient.inductionOn with
  | _ body => rfl

/-- Quotient renaming agrees with environment precomposition. -/
theorem denote_rename (I : Base → Type v) (η : Env I Δ) (ρ : Ren Γ Δ)
    (q : BetaEtaClass Base Γ A) :
    denote I η (rename ρ q) = denote I (Env.rename ρ η) q := by
  induction q using Quotient.inductionOn with
  | _ t => exact Tm.denote_rename I ρ t η

/-- Quotient substitution agrees with evaluation in the denotation of the
substitution. -/
theorem denote_subst (I : Base → Type v) (η : Env I Δ) (σ : Sub Γ Δ)
    (q : BetaEtaClass Base Γ A) :
    denote I η (subst σ q) =
      denote I (fun x => Tm.denote I (σ x) η) q := by
  induction q using Quotient.inductionOn with
  | _ t => exact Tm.denote_subst I σ t η

/-- The quotient beta law computes correctly in every model. -/
theorem denote_beta (I : Base → Type v) (η : Env I Γ)
    (body : BetaEtaClass Base (A :: Γ) B)
    (a : BetaEtaClass Base Γ A) :
    denote I η (app (lam body) a) = denote I η (instantiate body a) :=
  congrArg (denote I η) (beta body a)

/-- The quotient eta law is valid in every model. -/
theorem denote_eta (I : Base → Type v) (η : Env I Γ)
    (f : BetaEtaClass Base Γ (A ⇒ B)) :
    denote I η (lam (app (rename .succ f) (ofTm (.var .zero)))) =
      denote I η f :=
  congrArg (denote I η) (eta f)

/-- Every term model factors through the beta-eta quotient. -/
theorem denote_is_factor (I : Base → Type v) (η : Env I Γ) :
    (fun t : Tm Γ A => Tm.denote I t η) = denote I η ∘ ofTm := by
  funext t
  rfl

end BetaEtaClass

/-! ## Fibers of the canonical quotient map -/

namespace NbeClass

/-- Two embedded terms define the same observational class exactly when
their computed eta-long normal forms agree. -/
theorem ofTm_eq_iff {t u : Tm Γ A} : ofTm t = ofTm u ↔ NbeEq t u := by
  constructor
  · exact exact
  · exact sound

/-- Equality of observational classes is completely classified by their
normal-form observations. -/
theorem eq_iff_normalForm_eq {q r : NbeClass Base Γ A} :
    q = r ↔ normalForm q = normalForm r := by
  constructor
  · exact fun h => congrArg normalForm h
  · intro h
    apply (equivNormalForm (Base := Base) (Γ := Γ) (A := A)).injective
    exact h

/-- An observational class equals the class of its own canonical
representative. -/
theorem eq_ofNf_normalForm (q : NbeClass Base Γ A) :
    q = ofNf (normalForm q) := by
  apply (equivNormalForm (Base := Base) (Γ := Γ) (A := A)).injective
  exact (normalForm_ofNf (normalForm q)).symm

/-- Embedding normal forms into observational classes is injective. -/
theorem ofNf_injective : Function.Injective (@ofNf Base A Γ) := by
  intro n m h
  simpa only [normalForm_ofNf] using congrArg normalForm h

/-- Embedding normal forms into observational classes is surjective. -/
theorem ofNf_surjective : Function.Surjective (@ofNf Base A Γ) := by
  intro q
  exact ⟨normalForm q, (eq_ofNf_normalForm q).symm⟩

/-- The class of a normalized term is the original observational class. -/
theorem ofTm_normalizeTm (t : Tm Γ A) :
    ofTm (normalizeTm t) = ofTm t :=
  sound (NbeEq.normalize_left t)

/-- Every observational class is represented by an embedded source term. -/
theorem ofTm_surjective :
    Function.Surjective (@ofTm Base A Γ) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ t => exact ⟨t, rfl⟩

end NbeClass

/-- The canonical quotient map identifies two beta-eta classes exactly when
their normal-form observations agree. -/
theorem betaEtaToNbe_eq_iff {q r : BetaEtaClass Base Γ A} :
    betaEtaToNbe q = betaEtaToNbe r ↔
      BetaEtaClass.normalForm q = BetaEtaClass.normalForm r := by
  rw [NbeClass.eq_iff_normalForm_eq]
  simp only [normalForm_betaEtaToNbe]

/-- The fiber of the canonical quotient map on represented terms is NbE
equality. -/
theorem betaEtaToNbe_ofTm_eq_iff {t u : Tm Γ A} :
    betaEtaToNbe (BetaEtaClass.ofTm t) =
      betaEtaToNbe (BetaEtaClass.ofTm u) ↔ NbeEq t u := by
  simp only [betaEtaToNbe_ofTm, NbeClass.ofTm_eq_iff]

/-- Declarative conversion places represented terms in the same fiber of the
canonical quotient map. -/
theorem betaEtaToNbe_eq_of_betaEtaEq {t u : Tm Γ A} (h : BetaEtaEq t u) :
    betaEtaToNbe (BetaEtaClass.ofTm t) =
      betaEtaToNbe (BetaEtaClass.ofTm u) :=
  NbeClass.sound h.nbeEq

/-- Passing from beta-eta classes to observational classes commutes with
source renaming. -/
theorem betaEtaToNbe_rename (ρ : Ren Γ Δ)
    (q : BetaEtaClass Base Γ A) :
    betaEtaToNbe (BetaEtaClass.rename ρ q) =
      NbeClass.rename ρ (betaEtaToNbe q) := by
  induction q using Quotient.inductionOn with
  | _ t => rfl

/-! ## The remaining completeness criterion -/

/-- Syntactic completeness of beta-eta conversion for NbE equality at a
fixed context and type.  The semantic development above proves the converse
inclusion; this property names precisely the reverse direction. -/
def BetaEtaComplete (Base : Type u) (Γ : List (Ty Base)) (A : Ty Base) : Prop :=
  ∀ {t u : Tm Γ A}, NbeEq t u → BetaEtaEq t u

/-- Completeness says that every term is declaratively convertible to its
computed canonical representative. -/
theorem betaEtaComplete_iff_normalize (Base : Type u) (Γ : List (Ty Base))
    (A : Ty Base) :
    BetaEtaComplete Base Γ A ↔
      ∀ t : Tm Γ A, BetaEtaEq t (normalizeTm t) := by
  constructor
  · intro h t
    exact h (NbeEq.normalize_right t)
  · intro hnorm t u htu
    have hcanon : normalizeTm t = normalizeTm u :=
      NbeEq.iff_normalizeTm_eq.mp htu
    exact (hnorm t).trans ((BetaEtaEq.of_eq hcanon).trans (hnorm u).symm)

/-- Syntactic completeness is equivalent to injectivity of the canonical map
from beta-eta classes to observational classes. -/
theorem betaEtaComplete_iff_injective :
    BetaEtaComplete Base Γ A ↔
      Function.Injective
        (betaEtaToNbe (Base := Base) (Γ := Γ) (A := A)) := by
  constructor
  · intro h q r hqr
    induction q using Quotient.inductionOn with
    | _ t =>
      induction r using Quotient.inductionOn with
      | _ u =>
        apply BetaEtaClass.sound
        apply h
        exact NbeClass.exact hqr
  · intro hinj t u htu
    apply BetaEtaClass.exact
    apply hinj
    exact NbeClass.sound htu

/-- Completeness is equivalently injectivity of the normal-form observation
on beta-eta classes. -/
theorem betaEtaComplete_iff_normalForm_injective :
    BetaEtaComplete Base Γ A ↔
      Function.Injective
        (BetaEtaClass.normalForm (Base := Base) (Γ := Γ) (A := A)) := by
  rw [betaEtaComplete_iff_injective]
  constructor
  · intro h q r hqr
    apply h
    apply (NbeClass.equivNormalForm
      (Base := Base) (Γ := Γ) (A := A)).injective
    change NbeClass.normalForm (betaEtaToNbe q) =
      NbeClass.normalForm (betaEtaToNbe r)
    simpa only [normalForm_betaEtaToNbe] using hqr
  · intro h q r hqr
    apply h
    simpa only [normalForm_betaEtaToNbe] using
      congrArg NbeClass.normalForm hqr

/-- Completeness is equivalently the statement that equality of observed
normal forms reflects equality of beta-eta classes. -/
theorem betaEtaComplete_iff_normalForm_reflects :
    BetaEtaComplete Base Γ A ↔
      ∀ q r : BetaEtaClass Base Γ A,
        BetaEtaClass.normalForm q = BetaEtaClass.normalForm r → q = r := by
  rw [betaEtaComplete_iff_normalForm_injective]
  rfl

/-- Under completeness, every beta-eta class is represented by the erasure of
its own eta-long normal-form observation. -/
theorem betaEtaClass_eq_normalizeTm (h : BetaEtaComplete Base Γ A)
    (q : BetaEtaClass Base Γ A) :
    q = BetaEtaClass.ofTm (Nf.toTm (BetaEtaClass.normalForm q)) := by
  induction q using Quotient.inductionOn with
  | _ t =>
    apply BetaEtaClass.sound
    exact h (NbeEq.normalize_right t)

/-- Under completeness, embedded normal forms are surjective onto beta-eta
classes. -/
theorem betaEtaNormalForm_surjective (h : BetaEtaComplete Base Γ A) :
    Function.Surjective
      (fun n : Nf Γ A => BetaEtaClass.ofTm n.toTm) := by
  intro q
  exact ⟨BetaEtaClass.normalForm q, (betaEtaClass_eq_normalizeTm h q).symm⟩

/-- Embedded eta-long normal forms are always injective in the beta-eta
quotient, without assuming the reverse completeness direction. -/
theorem betaEtaNormalForm_injective :
    Function.Injective
      (fun n : Nf Γ A => BetaEtaClass.ofTm n.toTm) := by
  intro n m h
  have hn := congrArg BetaEtaClass.normalForm h
  simpa only [BetaEtaClass.normalForm_ofTm, normalizeNf_toTm] using hn

/-- Under syntactic completeness, beta-eta classes themselves have unique
eta-long normal-form representatives. -/
noncomputable def betaEtaEquivNormalForm (h : BetaEtaComplete Base Γ A) :
    Equiv (BetaEtaClass Base Γ A) (Nf Γ A) :=
  Equiv.trans
    (Equiv.ofBijective
      (betaEtaToNbe (Base := Base) (Γ := Γ) (A := A))
      ⟨betaEtaComplete_iff_injective.mp h, betaEtaToNbe_surjective⟩)
    NbeClass.equivNormalForm

/-- Under completeness, observing the normal form and embedding it back gives
the original beta-eta class. -/
theorem betaEtaClass_eq_normalForm (h : BetaEtaComplete Base Γ A)
    (q : BetaEtaClass Base Γ A) :
    q = (betaEtaEquivNormalForm h).symm (BetaEtaClass.normalForm q) := by
  apply (betaEtaEquivNormalForm h).injective
  simp only [Equiv.apply_symm_apply]
  induction q using Quotient.inductionOn with
  | _ t => rfl

end Cslib.Languages.LambdaCalculus.Stlc
