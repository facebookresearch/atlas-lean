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
# Beta-eta conversion and canonical normalization for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeSubstitution
public import Cslib.Foundations.Syntax.Congruence

/-!
# Beta-eta conversion and canonical normalization for STLC

This file connects normalization by evaluation to the intrinsic beta-eta
equational theory.  It first proves the computational beta and eta laws for
normalization, then packages them into typed declarative and operational
presentations of conversion.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u v

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Θ : List (Ty Base)}

/-- Interpreting a singleton syntactic substitution extends the semantic
identity environment by the interpretation of its distinguished image. -/
theorem SemEnv.evalSub_single_identity (a : Tm Γ A) :
    @SemEnv.evalSub Base (A :: Γ) Γ Γ (Sub.single a) SemEnv.identity =
      @SemEnv.cons Base A Γ Γ (nbeEval a SemEnv.identity)
        SemEnv.identity := by
  funext B x
  cases x with
  | zero => rfl
  | succ x => rfl

/-- Normalization computes a beta-redex by normalizing its instantiated body. -/
theorem normalizeNf_beta (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    normalizeNf (.app (.lam body) a) =
      normalizeNf (Tm.instantiate body a) := by
  rw [normalizeNf_instantiate]
  simp only [normalizeNf, nbeEval_app, nbeEval_lam_apply]
  rw [SemEnv.rename_id]
  rw [SemEnv.evalSub_single_identity]

/-- The term-level normalizer computes beta reduction as well. -/
theorem normalizeTm_beta (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    normalizeTm (.app (.lam body) a) =
      normalizeTm (Tm.instantiate body a) :=
  congrArg Nf.toTm (normalizeNf_beta body a)

/-- Normalization validates eta for functions. -/
theorem normalizeNf_eta (f : Tm Γ (A ⇒ B)) :
    normalizeNf (.lam (.app (Tm.weaken f) (.var .zero))) = normalizeNf f := by
  change Nf.lam
      (quote B (nbeEval (Tm.weaken (B := A) f)
        (SemEnv.cons (reflect A (.var .zero))
          (SemEnv.rename .succ SemEnv.identity)) Var.id
        (reflect A (.var .zero)))) =
    Nf.lam (quote B (nbeEval f SemEnv.identity .succ
      (reflect A (.var .zero))))
  apply congrArg Nf.lam
  let ξ : SemEnv (A :: Γ) (A :: Γ) :=
    SemEnv.cons (reflect A (.var .zero))
      (SemEnv.rename .succ SemEnv.identity)
  rw [Tm.weaken, nbeEval_rename_source]
  have hξ :
      @SemEnv.compRen Base Γ (A :: Γ) (A :: Γ) ξ
          (.succ : Ren Γ (A :: Γ)) =
        @SemEnv.rename Base Γ Γ (A :: Γ) .succ SemEnv.identity := by
    funext C x
    rfl
  rw [hξ]
  rw [← nbeEval_rename_sem f SemEnv.identity
    SemEnv.natural_identity (.succ : Ren Γ (A :: Γ))]
  simp only [Sem.rename_arr_apply]
  have hcomp :
      @Var.comp Base Γ (A :: Γ) (A :: Γ)
          (.succ : Ren Γ (A :: Γ))
          (Var.id : Ren (A :: Γ) (A :: Γ)) =
        (.succ : Ren Γ (A :: Γ)) := by
    funext C x
    rfl
  rw [hcomp]

/-- The term-level normalizer validates eta. -/
theorem normalizeTm_eta (f : Tm Γ (A ⇒ B)) :
    normalizeTm (.lam (.app (Tm.weaken f) (.var .zero))) = normalizeTm f :=
  congrArg Nf.toTm (normalizeNf_eta f)

/-! ## Declarative beta-eta conversion -/

/-- Typed beta-eta conversion, closed under equivalence and the term
constructors.  The relation is deliberately syntactic: unlike `ModelEq`, its
evidence records a finite equational derivation. -/
inductive BetaEtaEq {Base : Type u} :
    {Γ : List (Ty Base)} → {A : Ty Base} → Tm Γ A → Tm Γ A → Prop where
  | refl {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A) : BetaEtaEq t t
  | symm {Γ : List (Ty Base)} {A : Ty Base} {t u : Tm Γ A} :
      BetaEtaEq t u → BetaEtaEq u t
  | trans {Γ : List (Ty Base)} {A : Ty Base} {t u v : Tm Γ A} :
      BetaEtaEq t u → BetaEtaEq u v → BetaEtaEq t v
  | app {Γ : List (Ty Base)} {A B : Ty Base}
      {f g : Tm Γ (A ⇒ B)} {a b : Tm Γ A} :
      BetaEtaEq f g → BetaEtaEq a b → BetaEtaEq (.app f a) (.app g b)
  | lam {Γ : List (Ty Base)} {A B : Ty Base}
      {body body' : Tm (A :: Γ) B} :
      BetaEtaEq body body' → BetaEtaEq (.lam body) (.lam body')
  | beta {Γ : List (Ty Base)} {A B : Ty Base}
      (body : Tm (A :: Γ) B) (a : Tm Γ A) :
      BetaEtaEq (.app (.lam body) a) (Tm.instantiate body a)
  | eta {Γ : List (Ty Base)} {A B : Ty Base} (f : Tm Γ (A ⇒ B)) :
      BetaEtaEq (.lam (.app (Tm.weaken f) (.var .zero))) f

namespace BetaEtaEq

/-- Propositional equality embeds into beta-eta conversion. -/
theorem of_eq {t u : Tm Γ A} (h : t = u) : BetaEtaEq t u := h ▸ .refl t

/-- Conversion is preserved by function application on the left. -/
theorem app_left {f g : Tm Γ (A ⇒ B)} (h : BetaEtaEq f g) (a : Tm Γ A) :
    BetaEtaEq (.app f a) (.app g a) := .app h (.refl a)

/-- Conversion is preserved by function application on the right. -/
theorem app_right (f : Tm Γ (A ⇒ B)) {a b : Tm Γ A}
    (h : BetaEtaEq a b) : BetaEtaEq (.app f a) (.app f b) :=
  .app (.refl f) h

/-- Conversion is an equivalence relation at every context and type. -/
theorem equivalence : Equivalence (@BetaEtaEq Base Γ A) :=
  ⟨fun t => .refl t, fun h => .symm h, fun h₁ h₂ => .trans h₁ h₂⟩

/-- Every typed one-hole term context preserves beta-eta conversion. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : BetaEtaEq t u) : BetaEtaEq (C.plug t) (C.plug u) := by
  induction C with
  | hole => exact h
  | appFun C a ih => exact ih.app_left a
  | appArg f C ih => exact ih.app_right f
  | lam C ih => exact .lam ih

/-- Beta conversion remains valid inside an arbitrary typed context. -/
theorem context_beta (C : TmCtx Γ B Δ C) (body : Tm (A :: Γ) B)
    (a : Tm Γ A) :
    BetaEtaEq (C.plug (.app (.lam body) a))
      (C.plug (Tm.instantiate body a)) :=
  context C (.beta body a)

/-- Eta conversion remains valid inside an arbitrary typed context. -/
theorem context_eta (C : TmCtx Γ (A ⇒ B) Δ C) (f : Tm Γ (A ⇒ B)) :
    BetaEtaEq (C.plug (.lam (.app (Tm.weaken f) (.var .zero))))
      (C.plug f) :=
  context C (.eta f)

/-- Renaming every free variable preserves a beta-eta derivation. -/
theorem rename {t u : Tm Γ A} (h : BetaEtaEq t u) (ρ : Ren Γ Δ) :
    BetaEtaEq (Tm.rename ρ t) (Tm.rename ρ u) := by
  induction h generalizing Δ with
  | refl t => exact .refl _
  | symm h ih => exact .symm (ih ρ)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | app hf ha ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam h ih => exact .lam (ih (Var.lift ρ))
  | @beta Γ A B body a =>
      simpa only [Tm.rename_app, Tm.rename_lam, Tm.rename_instantiate]
        using BetaEtaEq.beta (Tm.rename (Var.lift ρ) body) (Tm.rename ρ a)
  | @eta Γ A B f =>
      simpa only [Tm.rename_lam, Tm.rename_app, Tm.rename_var,
        Tm.rename_weaken, Var.lift_zero]
        using BetaEtaEq.eta (Tm.rename ρ f)

/-- Simultaneous capture-avoiding substitution preserves conversion. -/
theorem subst {t u : Tm Γ A} (h : BetaEtaEq t u) (σ : Sub Γ Δ) :
    BetaEtaEq (Tm.subst σ t) (Tm.subst σ u) := by
  induction h generalizing Δ with
  | refl t => exact .refl _
  | symm h ih => exact .symm (ih σ)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | app hf ha ihf iha => exact .app (ihf σ) (iha σ)
  | lam h ih => exact .lam (ih (Sub.lift σ))
  | @beta Γ A B body a =>
      simpa only [Tm.subst_app, Tm.subst_lam, Tm.subst_instantiate]
        using BetaEtaEq.beta (Tm.subst (Sub.lift σ) body) (Tm.subst σ a)
  | @eta Γ A B f =>
      simpa only [Tm.subst_lam, Tm.subst_app, Tm.subst_var,
        Tm.subst_lift_weaken, Sub.lift_zero]
        using BetaEtaEq.eta (Tm.subst σ f)

/-- A term preserves pointwise conversion between two substitutions. -/
theorem subst_congr_right (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : ∀ {B} (x : Var Γ B), BetaEtaEq (σ x) (τ x)) :
    BetaEtaEq (Tm.subst σ t) (Tm.subst τ t) := by
  induction t generalizing Δ with
  | var x => exact h x
  | app f a ihf iha => exact .app (ihf h) (iha h)
  | @lam A B Γ body ih =>
      apply BetaEtaEq.lam
      apply ih
      intro C x
      cases x with
      | zero => exact .refl _
      | succ x =>
        exact (h x).rename (.succ : Ren Δ (A :: Δ))

/-- Instantiating the newest variable preserves conversion of open bodies. -/
theorem instantiate {body body' : Tm (A :: Γ) B}
    (h : BetaEtaEq body body') (a : Tm Γ A) :
    BetaEtaEq (Tm.instantiate body a) (Tm.instantiate body' a) :=
  h.subst (Sub.single a)

/-- Instantiation is also congruent in the argument. -/
theorem instantiate_arg (body : Tm (A :: Γ) B) {a a' : Tm Γ A}
    (h : BetaEtaEq a a') :
    BetaEtaEq (Tm.instantiate body a) (Tm.instantiate body a') := by
  apply subst_congr_right body
  intro C x
  cases x with
  | zero => exact h
  | succ x => exact .refl _

/-- Instantiation is congruent in both its body and argument. -/
theorem instantiate_congr {body body' : Tm (A :: Γ) B}
    {a a' : Tm Γ A} (hbody : BetaEtaEq body body')
    (ha : BetaEtaEq a a') :
    BetaEtaEq (Tm.instantiate body a) (Tm.instantiate body' a') :=
  (hbody.instantiate a).trans (instantiate_arg body' ha)

/-- Every syntactic conversion is sound in any fixed set-theoretic model. -/
theorem semEq (I : Base → Type v) {t u : Tm Γ A} (h : BetaEtaEq t u) :
    SemEq I t u := by
  induction h with
  | refl t => exact SemEq.refl I t
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | app hf ha ihf iha => exact SemEq.app ihf iha
  | lam h ih => exact SemEq.lam ih
  | beta body a => exact SemEq.beta I body a
  | eta f => exact SemEq.eta I f

/-- Every syntactic beta-eta conversion is valid in all same-universe models. -/
theorem modelEq {t u : Tm Γ A} (h : BetaEtaEq t u) : ModelEq t u :=
  fun I => h.semEq I

end BetaEtaEq

/-- Beta-eta conversion is a congruence in the sense of the upstream `Congruence` class. -/
instance BetaEtaEq.instCongruence : Congruence (@BetaEtaEq Base Γ A) := ⟨⟩

/-- Beta-eta conversion is an upstream `LawfulCongruence`: an equivalence relation preserved
by every typed one-hole context (`BetaEtaEq.context`). -/
instance BetaEtaEq.instLawfulCongruence : LawfulCongruence (@BetaEtaEq Base Γ A) where
  refl := BetaEtaEq.refl
  symm _ _ := BetaEtaEq.symm
  trans _ _ _ := BetaEtaEq.trans
  covariant := ⟨fun C _ _ h => BetaEtaEq.context (C : TmCtx Γ A Γ A) h⟩

/-! ## Directed beta-eta reduction -/

/-- One compatible beta-eta contraction.  Congruence constructors expose the
exact subterm in which the contraction occurs. -/
inductive BetaEtaStep {Base : Type u} :
    {Γ : List (Ty Base)} → {A : Ty Base} → Tm Γ A → Tm Γ A → Prop where
  | beta {Γ : List (Ty Base)} {A B : Ty Base}
      (body : Tm (A :: Γ) B) (a : Tm Γ A) :
      BetaEtaStep (.app (.lam body) a) (Tm.instantiate body a)
  | eta {Γ : List (Ty Base)} {A B : Ty Base} (f : Tm Γ (A ⇒ B)) :
      BetaEtaStep (.lam (.app (Tm.weaken f) (.var .zero))) f
  | appFun {Γ : List (Ty Base)} {A B : Ty Base}
      {f g : Tm Γ (A ⇒ B)} (h : BetaEtaStep f g) (a : Tm Γ A) :
      BetaEtaStep (.app f a) (.app g a)
  | appArg {Γ : List (Ty Base)} {A B : Ty Base}
      (f : Tm Γ (A ⇒ B)) {a b : Tm Γ A} (h : BetaEtaStep a b) :
      BetaEtaStep (.app f a) (.app f b)
  | lam {Γ : List (Ty Base)} {A B : Ty Base}
      {body body' : Tm (A :: Γ) B} (h : BetaEtaStep body body') :
      BetaEtaStep (.lam body) (.lam body')

namespace BetaEtaStep

/-- A directed contraction is a declarative conversion. -/
theorem betaEtaEq {t u : Tm Γ A} (h : BetaEtaStep t u) : BetaEtaEq t u := by
  induction h with
  | beta body a => exact .beta body a
  | eta f => exact .eta f
  | appFun h a ih => exact ih.app_left a
  | appArg f h ih => exact ih.app_right f
  | lam h ih => exact .lam ih

/-- Renaming commutes with one compatible contraction. -/
theorem rename {t u : Tm Γ A} (h : BetaEtaStep t u) (ρ : Ren Γ Δ) :
    BetaEtaStep (Tm.rename ρ t) (Tm.rename ρ u) := by
  induction h generalizing Δ with
  | @beta Γ A B body a =>
      simpa only [Tm.rename_app, Tm.rename_lam, Tm.rename_instantiate]
        using BetaEtaStep.beta (Tm.rename (Var.lift ρ) body) (Tm.rename ρ a)
  | @eta Γ A B f =>
      simpa only [Tm.rename_lam, Tm.rename_app, Tm.rename_var,
        Tm.rename_weaken, Var.lift_zero]
        using BetaEtaStep.eta (Tm.rename ρ f)
  | appFun h a ih => exact .appFun (ih ρ) (Tm.rename ρ a)
  | appArg f h ih => exact .appArg (Tm.rename ρ f) (ih ρ)
  | lam h ih => exact .lam (ih (Var.lift ρ))

/-- Substitution commutes with one compatible contraction. -/
theorem subst {t u : Tm Γ A} (h : BetaEtaStep t u) (σ : Sub Γ Δ) :
    BetaEtaStep (Tm.subst σ t) (Tm.subst σ u) := by
  induction h generalizing Δ with
  | @beta Γ A B body a =>
      simpa only [Tm.subst_app, Tm.subst_lam, Tm.subst_instantiate]
        using BetaEtaStep.beta (Tm.subst (Sub.lift σ) body) (Tm.subst σ a)
  | @eta Γ A B f =>
      simpa only [Tm.subst_lam, Tm.subst_app, Tm.subst_var,
        Tm.subst_lift_weaken, Sub.lift_zero]
        using BetaEtaStep.eta (Tm.subst σ f)
  | appFun h a ih => exact .appFun (ih σ) (Tm.subst σ a)
  | appArg f h ih => exact .appArg (Tm.subst σ f) (ih σ)
  | lam h ih => exact .lam (ih (Sub.lift σ))

/-- Plugging one contraction into a typed context gives one contraction. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : BetaEtaStep t u) : BetaEtaStep (C.plug t) (C.plug u) := by
  induction C with
  | hole => exact h
  | appFun C a ih => exact .appFun ih a
  | appArg f C ih => exact .appArg f ih
  | lam C ih => exact .lam ih

/-- A contraction is sound in every fixed set-theoretic model. -/
theorem semEq (I : Base → Type v) {t u : Tm Γ A} (h : BetaEtaStep t u) :
    SemEq I t u := h.betaEtaEq.semEq I

/-- A contraction is model-independent semantic equality. -/
theorem modelEq {t u : Tm Γ A} (h : BetaEtaStep t u) : ModelEq t u :=
  h.betaEtaEq.modelEq

/-- A root beta contraction remains one step inside a typed context. -/
theorem context_beta (C : TmCtx Γ B Δ C) (body : Tm (A :: Γ) B)
    (a : Tm Γ A) :
    BetaEtaStep (C.plug (.app (.lam body) a))
      (C.plug (Tm.instantiate body a)) :=
  context C (.beta body a)

/-- A root eta contraction remains one step inside a typed context. -/
theorem context_eta (C : TmCtx Γ (A ⇒ B) Δ C) (f : Tm Γ (A ⇒ B)) :
    BetaEtaStep (C.plug (.lam (.app (Tm.weaken f) (.var .zero))))
      (C.plug f) :=
  context C (.eta f)

end BetaEtaStep

/-- Reflexive-transitive beta-eta reduction. -/
abbrev BetaEtaSteps {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} :=
  Relation.ReflTransGen (@BetaEtaStep Base Γ A)

namespace BetaEtaSteps

/-- Regard a single contraction as a reduction sequence. -/
theorem single {t u : Tm Γ A} (h : BetaEtaStep t u) : BetaEtaSteps t u :=
  .tail .refl h

/-- Concatenate two reduction sequences. -/
theorem trans {t u v : Tm Γ A} (h₁ : BetaEtaSteps t u)
    (h₂ : BetaEtaSteps u v) : BetaEtaSteps t v := by
  induction h₂ with
  | refl => exact h₁
  | tail h step ih => exact .tail ih step

/-- Append one final contraction. -/
theorem step_right {t u v : Tm Γ A} (h : BetaEtaSteps t u)
    (step : BetaEtaStep u v) : BetaEtaSteps t v := .tail h step

/-- Prepend one contraction to a reduction sequence. -/
theorem step_left {t u v : Tm Γ A} (step : BetaEtaStep t u)
    (h : BetaEtaSteps u v) : BetaEtaSteps t v := (single step).trans h

/-- Every reduction sequence is a declarative beta-eta conversion. -/
theorem betaEtaEq {t u : Tm Γ A} (h : BetaEtaSteps t u) : BetaEtaEq t u := by
  induction h with
  | refl => exact .refl _
  | tail h step ih => exact ih.trans step.betaEtaEq

/-- Renaming every term in a reduction sequence preserves the sequence. -/
theorem rename {t u : Tm Γ A} (h : BetaEtaSteps t u) (ρ : Ren Γ Δ) :
    BetaEtaSteps (Tm.rename ρ t) (Tm.rename ρ u) := by
  induction h with
  | refl => exact .refl
  | tail h step ih => exact .tail ih (step.rename ρ)

/-- Substitution through every term in a reduction sequence preserves it. -/
theorem subst {t u : Tm Γ A} (h : BetaEtaSteps t u) (σ : Sub Γ Δ) :
    BetaEtaSteps (Tm.subst σ t) (Tm.subst σ u) := by
  induction h with
  | refl => exact .refl
  | tail h step ih => exact .tail ih (step.subst σ)

/-- A typed context maps an entire reduction sequence pointwise. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : BetaEtaSteps t u) : BetaEtaSteps (C.plug t) (C.plug u) := by
  induction h with
  | refl => exact .refl
  | tail h step ih => exact .tail ih (step.context C)

/-- Function application maps a reduction sequence in function position. -/
theorem app_left {f g : Tm Γ (A ⇒ B)} (h : BetaEtaSteps f g) (a : Tm Γ A) :
    BetaEtaSteps (.app f a) (.app g a) :=
  h.context (.appFun .hole a)

/-- Function application maps a reduction sequence in argument position. -/
theorem app_right (f : Tm Γ (A ⇒ B)) {a b : Tm Γ A}
    (h : BetaEtaSteps a b) : BetaEtaSteps (.app f a) (.app f b) :=
  h.context (.appArg f .hole)

/-- Lambda abstraction maps a reduction sequence in its body. -/
theorem lam {body body' : Tm (A :: Γ) B} (h : BetaEtaSteps body body') :
    BetaEtaSteps (.lam body) (.lam body') := h.context (.lam .hole)

/-- Multi-step reduction is sound in every fixed model. -/
theorem semEq (I : Base → Type v) {t u : Tm Γ A} (h : BetaEtaSteps t u) :
    SemEq I t u := h.betaEtaEq.semEq I

/-- Multi-step reduction is sound in all same-universe models. -/
theorem modelEq {t u : Tm Γ A} (h : BetaEtaSteps t u) : ModelEq t u :=
  h.betaEtaEq.modelEq

end BetaEtaSteps

/-! ## Pointwise conversion of substitutions -/

/-- Two substitutions are beta-eta equal when all corresponding images are
beta-eta equal. -/
def SubBetaEtaEq (σ τ : Sub Γ Δ) : Prop :=
  ∀ {A} (x : Var Γ A), BetaEtaEq (σ x) (τ x)

namespace SubBetaEtaEq

/-- Pointwise conversion is reflexive. -/
theorem refl (σ : Sub Γ Δ) : SubBetaEtaEq σ σ := fun _ => .refl _

/-- Pointwise conversion is symmetric. -/
theorem symm {σ τ : Sub Γ Δ} (h : SubBetaEtaEq σ τ) : SubBetaEtaEq τ σ :=
  fun x => (h x).symm

/-- Pointwise conversion is transitive. -/
theorem trans {σ τ υ : Sub Γ Δ} (h₁ : SubBetaEtaEq σ τ)
    (h₂ : SubBetaEtaEq τ υ) : SubBetaEtaEq σ υ :=
  fun x => (h₁ x).trans (h₂ x)

/-- Pointwise conversion is an equivalence relation on substitutions. -/
theorem equivalence : Equivalence (@SubBetaEtaEq Base Γ Δ) :=
  ⟨refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Extending related substitutions by related images preserves relatedness. -/
theorem cons {a b : Tm Δ A} {s t : Sub Γ Δ} (hab : BetaEtaEq a b)
    (hst : SubBetaEtaEq s t) :
    SubBetaEtaEq (Sub.cons a s) (Sub.cons b t) := by
  intro C x
  cases x with
  | zero => exact hab
  | succ x => exact hst x

/-- Lifting related substitutions under a binder preserves relatedness. -/
theorem lift {σ τ : Sub Γ Δ} (h : SubBetaEtaEq σ τ) :
    SubBetaEtaEq (Sub.lift (A := A) σ) (Sub.lift τ) := by
  intro B x
  cases x with
  | zero => exact .refl _
  | succ x => exact (h x).rename (.succ : Ren Δ (A :: Δ))

/-- Renaming the codomain of related substitutions preserves relatedness. -/
theorem rename {σ τ : Sub Γ Δ} (h : SubBetaEtaEq σ τ) (ρ : Ren Δ Θ) :
    SubBetaEtaEq (Sub.rename σ ρ) (Sub.rename τ ρ) :=
  fun x => (h x).rename ρ

/-- Postcomposing related substitutions with the same substitution preserves
their pointwise conversion. -/
theorem comp_left {σ τ : Sub Γ Δ} (h : SubBetaEtaEq σ τ)
    (υ : Sub Δ Θ) : SubBetaEtaEq (Sub.comp σ υ) (Sub.comp τ υ) :=
  fun x => (h x).subst υ

/-- Precomposing one substitution with pointwise-related codomain
substitutions preserves pointwise conversion. -/
theorem comp_right (σ : Sub Γ Δ) {τ υ : Sub Δ Θ}
    (h : SubBetaEtaEq τ υ) :
    SubBetaEtaEq (Sub.comp σ τ) (Sub.comp σ υ) :=
  fun x => BetaEtaEq.subst_congr_right (σ x) h

/-- Composition is congruent in both substitutions. -/
theorem comp_congr {σ σ' : Sub Γ Δ} {τ τ' : Sub Δ Θ}
    (hσ : SubBetaEtaEq σ σ') (hτ : SubBetaEtaEq τ τ') :
    SubBetaEtaEq (Sub.comp σ τ) (Sub.comp σ' τ') :=
  SubBetaEtaEq.trans (hσ.comp_left τ) (SubBetaEtaEq.comp_right σ' hτ)

/-- Pointwise syntactic conversion implies pointwise equality in every fixed
set-theoretic model. -/
theorem subSemEq (I : Base → Type v) {σ τ : Sub Γ Δ}
    (h : SubBetaEtaEq σ τ) : SubSemEq I σ τ :=
  fun x η => h x |>.semEq I η

end SubBetaEtaEq

namespace BetaEtaEq

/-- Substitution is jointly congruent in the converted term and in every
image of the converted substitution. -/
theorem subst_congr {t u : Tm Γ A} {σ τ : Sub Γ Δ}
    (htu : BetaEtaEq t u) (hστ : SubBetaEtaEq σ τ) :
    BetaEtaEq (Tm.subst σ t) (Tm.subst τ u) :=
  (htu.subst σ).trans (subst_congr_right u hστ)

/-- Pointwise conversion of substitutions gives a declarative conversion
after substitution into any fixed term. -/
theorem subst_pointwise (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : SubBetaEtaEq σ τ) :
    BetaEtaEq (Tm.subst σ t) (Tm.subst τ t) :=
  subst_congr_right t h

end BetaEtaEq

/-! ## Joinability -/

/-- Two terms are beta-eta joinable when they reduce to a common term. -/
abbrev BetaEtaJoin {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} :=
  Relation.Join (@BetaEtaSteps Base Γ A)

namespace BetaEtaJoin

/-- Every term is joinable with itself. -/
theorem refl (t : Tm Γ A) : BetaEtaJoin t t :=
  ⟨t, .refl, .refl⟩

/-- Joinability is symmetric. -/
theorem symm {t u : Tm Γ A} (h : BetaEtaJoin t u) : BetaEtaJoin u t := by
  rcases h with ⟨v, ht, hu⟩
  exact ⟨v, hu, ht⟩

/-- Joinable terms are declaratively beta-eta equal. -/
theorem betaEtaEq {t u : Tm Γ A} (h : BetaEtaJoin t u) : BetaEtaEq t u := by
  rcases h with ⟨v, ht, hu⟩
  exact ht.betaEtaEq.trans hu.betaEtaEq.symm

/-- Joinability is preserved by renaming. -/
theorem rename {t u : Tm Γ A} (h : BetaEtaJoin t u) (ρ : Ren Γ Δ) :
    BetaEtaJoin (Tm.rename ρ t) (Tm.rename ρ u) := by
  rcases h with ⟨v, ht, hu⟩
  exact ⟨Tm.rename ρ v, ht.rename ρ, hu.rename ρ⟩

/-- Joinability is preserved by substitution. -/
theorem subst {t u : Tm Γ A} (h : BetaEtaJoin t u) (σ : Sub Γ Δ) :
    BetaEtaJoin (Tm.subst σ t) (Tm.subst σ u) := by
  rcases h with ⟨v, ht, hu⟩
  exact ⟨Tm.subst σ v, ht.subst σ, hu.subst σ⟩

/-- Joinability is preserved by every typed one-hole context. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : BetaEtaJoin t u) : BetaEtaJoin (C.plug t) (C.plug u) := by
  rcases h with ⟨v, ht, hu⟩
  exact ⟨C.plug v, ht.context C, hu.context C⟩

/-- Joinability is sound in every same-universe model. -/
theorem modelEq {t u : Tm Γ A} (h : BetaEtaJoin t u) : ModelEq t u :=
  h.betaEtaEq.modelEq

end BetaEtaJoin

/-! ## Zigzag presentation of conversion -/

/-- A beta-eta conversion path is the equivalence closure of compatible
contraction. -/
abbrev BetaEtaZigzag {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} :=
  Relation.EqvGen (@BetaEtaStep Base Γ A)

namespace BetaEtaZigzag

/-- A forward contraction is a one-edge zigzag. -/
theorem of_step {t u : Tm Γ A} (h : BetaEtaStep t u) : BetaEtaZigzag t u :=
  .rel t u h

/-- A backward contraction is a one-edge zigzag. -/
theorem of_step_symm {t u : Tm Γ A} (h : BetaEtaStep t u) : BetaEtaZigzag u t :=
  .symm t u (.rel t u h)

/-- Append one zigzag to another. -/
theorem trans {t u v : Tm Γ A} (h₁ : BetaEtaZigzag t u)
    (h₂ : BetaEtaZigzag u v) : BetaEtaZigzag t v :=
  Relation.EqvGen.trans t u v h₁ h₂

/-- Reverse every edge of a zigzag. -/
theorem symm {t u : Tm Γ A} (h : BetaEtaZigzag t u) : BetaEtaZigzag u t :=
  Relation.EqvGen.symm t u h

/-- Conversion paths form an equivalence relation. -/
theorem equivalence : Equivalence (@BetaEtaZigzag Base Γ A) :=
  Relation.EqvGen.is_equivalence _

/-- Declarative conversion extracted from a zigzag. -/
theorem betaEtaEq {t u : Tm Γ A} (h : BetaEtaZigzag t u) : BetaEtaEq t u := by
  induction h with
  | rel t u step => exact step.betaEtaEq
  | refl => exact .refl _
  | symm t u h ih => exact ih.symm
  | trans t u v h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Map a zigzag through function position of an application. -/
theorem app_left {f g : Tm Γ (A ⇒ B)} (h : BetaEtaZigzag f g) (a : Tm Γ A) :
    BetaEtaZigzag (.app f a) (.app g a) := by
  induction h with
  | rel f g step => exact of_step (.appFun step a)
  | refl => exact .refl _
  | symm f g h ih => exact ih.symm
  | trans f g k h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Map a zigzag through argument position of an application. -/
theorem app_right (f : Tm Γ (A ⇒ B)) {a b : Tm Γ A}
    (h : BetaEtaZigzag a b) : BetaEtaZigzag (.app f a) (.app f b) := by
  induction h with
  | rel a b step => exact of_step (.appArg f step)
  | refl => exact .refl _
  | symm a b h ih => exact ih.symm
  | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Map a zigzag under lambda abstraction. -/
theorem lam {body body' : Tm (A :: Γ) B} (h : BetaEtaZigzag body body') :
    BetaEtaZigzag (.lam body) (.lam body') := by
  induction h with
  | rel body body' step => exact of_step (.lam step)
  | refl => exact .refl _
  | symm body body' h ih => exact ih.symm
  | trans body body' body'' h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Every declarative beta-eta conversion can be linearized as a zigzag of
compatible root contractions. -/
theorem of_betaEtaEq {t u : Tm Γ A} (h : BetaEtaEq t u) : BetaEtaZigzag t u := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | app hf ha ihf iha => exact (ihf.app_left _).trans (iha.app_right _)
  | lam h ih => exact ih.lam
  | beta body a => exact of_step (.beta body a)
  | eta f => exact of_step (.eta f)

/-- Renaming maps every edge of a conversion path. -/
theorem rename {t u : Tm Γ A} (h : BetaEtaZigzag t u) (ρ : Ren Γ Δ) :
    BetaEtaZigzag (Tm.rename ρ t) (Tm.rename ρ u) := by
  induction h with
  | rel t u step => exact of_step (step.rename ρ)
  | refl => exact .refl _
  | symm t u h ih => exact ih.symm
  | trans t u v h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Substitution maps every edge of a conversion path. -/
theorem subst {t u : Tm Γ A} (h : BetaEtaZigzag t u) (σ : Sub Γ Δ) :
    BetaEtaZigzag (Tm.subst σ t) (Tm.subst σ u) := by
  induction h with
  | rel t u step => exact of_step (step.subst σ)
  | refl => exact .refl _
  | symm t u h ih => exact ih.symm
  | trans t u v h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Typed contexts map every edge of a conversion path. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : BetaEtaZigzag t u) : BetaEtaZigzag (C.plug t) (C.plug u) := by
  induction h with
  | rel t u step => exact of_step (step.context C)
  | refl => exact .refl _
  | symm t u h ih => exact ih.symm
  | trans t u v h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Zigzag conversion is sound in a fixed model. -/
theorem semEq (I : Base → Type v) {t u : Tm Γ A} (h : BetaEtaZigzag t u) :
    SemEq I t u := h.betaEtaEq.semEq I

/-- Zigzag conversion is sound in all same-universe models. -/
theorem modelEq {t u : Tm Γ A} (h : BetaEtaZigzag t u) : ModelEq t u :=
  h.betaEtaEq.modelEq

end BetaEtaZigzag

/-- The declarative and path presentations of beta-eta conversion coincide. -/
theorem betaEtaEq_iff_zigzag {t u : Tm Γ A} :
    BetaEtaEq t u ↔ BetaEtaZigzag t u :=
  ⟨BetaEtaZigzag.of_betaEtaEq, BetaEtaZigzag.betaEtaEq⟩

/-! ## Pointwise zigzag conversion of substitutions -/

/-- Two substitutions are connected pointwise when corresponding images are
connected by finite beta-eta zigzags.  This is the path-level counterpart of
`SubBetaEtaEq`, useful when a client needs an explicit sequence of compatible
contractions rather than only the generated equivalence relation. -/
def SubBetaEtaZigzag (σ τ : Sub Γ Δ) : Prop :=
  ∀ {A} (x : Var Γ A), BetaEtaZigzag (σ x) (τ x)

namespace SubBetaEtaZigzag

/-- Every substitution is pointwise connected to itself. -/
theorem refl (σ : Sub Γ Δ) : SubBetaEtaZigzag σ σ :=
  fun _ => .refl _

/-- Reverse every component path of pointwise substitution conversion. -/
theorem symm {σ τ : Sub Γ Δ} (h : SubBetaEtaZigzag σ τ) :
    SubBetaEtaZigzag τ σ :=
  fun x => (h x).symm

/-- Concatenate component paths of pointwise substitution conversion. -/
theorem trans {σ τ υ : Sub Γ Δ} (h₁ : SubBetaEtaZigzag σ τ)
    (h₂ : SubBetaEtaZigzag τ υ) : SubBetaEtaZigzag σ υ :=
  fun x => (h₁ x).trans (h₂ x)

/-- Pointwise path conversion is an equivalence relation. -/
theorem equivalence : Equivalence (@SubBetaEtaZigzag Base Γ Δ) :=
  ⟨refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Extending pointwise-connected substitutions by connected terms preserves
pointwise path conversion. -/
theorem cons {a b : Tm Δ A} {s t : Sub Γ Δ} (hab : BetaEtaZigzag a b)
    (hst : SubBetaEtaZigzag s t) :
    SubBetaEtaZigzag (Sub.cons a s) (Sub.cons b t) := by
  intro C x
  cases x with
  | zero => exact hab
  | succ x => exact hst x

/-- Lifting pointwise-connected substitutions through a binder preserves
their component paths. -/
theorem lift {σ τ : Sub Γ Δ} (h : SubBetaEtaZigzag σ τ) :
    SubBetaEtaZigzag (Sub.lift (A := A) σ) (Sub.lift τ) := by
  intro B x
  cases x with
  | zero => exact .refl _
  | succ x => exact (h x).rename (.succ : Ren Δ (A :: Δ))

/-- Renaming every image maps pointwise substitution paths. -/
theorem rename {σ τ : Sub Γ Δ} (h : SubBetaEtaZigzag σ τ) (ρ : Ren Δ Θ) :
    SubBetaEtaZigzag (Sub.rename σ ρ) (Sub.rename τ ρ) :=
  fun x => (h x).rename ρ

/-- Postcomposing pointwise-connected substitutions with one substitution
maps every component path. -/
theorem comp_left {σ τ : Sub Γ Δ} (h : SubBetaEtaZigzag σ τ)
    (υ : Sub Δ Θ) : SubBetaEtaZigzag (Sub.comp σ υ) (Sub.comp τ υ) :=
  fun x => (h x).subst υ

/-- Precomposing with one substitution preserves pointwise path conversion
of codomain substitutions. -/
theorem comp_right (σ : Sub Γ Δ) {τ υ : Sub Δ Θ}
    (h : SubBetaEtaZigzag τ υ) :
    SubBetaEtaZigzag (Sub.comp σ τ) (Sub.comp σ υ) :=
  fun x => BetaEtaZigzag.of_betaEtaEq
    (BetaEtaEq.subst_congr_right (σ x) (fun y => (h y).betaEtaEq))

/-- Composition is congruent in paths in both substitutions. -/
theorem comp_congr {σ σ' : Sub Γ Δ} {τ τ' : Sub Δ Θ}
    (hσ : SubBetaEtaZigzag σ σ') (hτ : SubBetaEtaZigzag τ τ') :
    SubBetaEtaZigzag (Sub.comp σ τ) (Sub.comp σ' τ') :=
  SubBetaEtaZigzag.trans (hσ.comp_left τ)
    (SubBetaEtaZigzag.comp_right σ' hτ)

/-- Forgetting the explicit paths gives pointwise declarative conversion. -/
theorem subBetaEtaEq {σ τ : Sub Γ Δ} (h : SubBetaEtaZigzag σ τ) :
    SubBetaEtaEq σ τ :=
  fun x => (h x).betaEtaEq

/-- Every pointwise declarative substitution conversion admits component
zigzag witnesses. -/
theorem of_subBetaEtaEq {σ τ : Sub Γ Δ} (h : SubBetaEtaEq σ τ) :
    SubBetaEtaZigzag σ τ :=
  fun x => BetaEtaZigzag.of_betaEtaEq (h x)

end SubBetaEtaZigzag

namespace BetaEtaZigzag

/-- Substitution is jointly congruent in a term path and pointwise paths for
the substituted images. -/
theorem subst_congr {t u : Tm Γ A} {σ τ : Sub Γ Δ}
    (htu : BetaEtaZigzag t u) (hστ : SubBetaEtaZigzag σ τ) :
    BetaEtaZigzag (Tm.subst σ t) (Tm.subst τ u) :=
  of_betaEtaEq (htu.betaEtaEq.subst_congr hστ.subBetaEtaEq)

/-- Pointwise paths between substitutions induce a path after substitution
into a fixed term. -/
theorem subst_pointwise (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : SubBetaEtaZigzag σ τ) :
    BetaEtaZigzag (Tm.subst σ t) (Tm.subst τ t) :=
  subst_congr (.refl t) h

end BetaEtaZigzag

/-- The declarative and explicit-path presentations of pointwise substitution
conversion coincide. -/
theorem subBetaEtaEq_iff_zigzag {σ τ : Sub Γ Δ} :
    SubBetaEtaEq σ τ ↔ SubBetaEtaZigzag σ τ :=
  ⟨SubBetaEtaZigzag.of_subBetaEtaEq, SubBetaEtaZigzag.subBetaEtaEq⟩

end Cslib.Languages.LambdaCalculus.Stlc
