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
# Syntactic completeness of STLC normalization by evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeCompleteness

/-!
# Syntactic completeness of normalization by evaluation

This module supplies the missing reverse direction of the NbE correctness
story.  A type-indexed syntactic logical relation connects semantic values to
terms.  Reflection and reification form the two halves of its fundamental
lemma, from which every term is beta-eta convertible to its computed normal
form.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Θ : List (Ty Base)}

/-- A semantic value and a term are syntactically related when they agree at
base type and related functions take related arguments to related results in
every future context. -/
def SyntacticRelated : {Γ : List (Ty Base)} →
    (A : Ty Base) → Sem Γ A → Tm Γ A → Prop
  | _, .base _, n, t => BetaEtaEq n.toTm t
  | Γ, A ⇒ B, f, t => ∀ {Δ} (ρ : Ren Γ Δ) (a : Sem Δ A) (s : Tm Δ A),
      SyntacticRelated A a s →
      SyntacticRelated B (f ρ a) (.app (.rename ρ t) s)

@[simp] theorem syntacticRelated_base {b : Base} (n : Sem Γ (.base b))
    (t : Tm Γ (.base b)) :
    SyntacticRelated (.base b) n t ↔ BetaEtaEq n.toTm t := Iff.rfl

@[simp] theorem syntacticRelated_arr (f : Sem Γ (A ⇒ B)) (t : Tm Γ (A ⇒ B)) :
    SyntacticRelated (A ⇒ B) f t ↔
      ∀ {Δ} (ρ : Ren Γ Δ) (a : Sem Δ A) (s : Tm Δ A),
        SyntacticRelated A a s →
        SyntacticRelated B (f ρ a) (.app (.rename ρ t) s) := Iff.rfl

/-- The syntactic logical relation is stable under beta-eta conversion of its
term component. -/
theorem SyntacticRelated.congr (A : Ty Base) {v : Sem Γ A}
    {t s : Tm Γ A} (hv : SyntacticRelated A v t) (h : BetaEtaEq t s) :
    SyntacticRelated A v s := by
  induction A generalizing Γ with
  | base b => exact hv.trans h
  | arr A B ihA ihB =>
      intro Δ ρ a q ha
      exact ihB (hv ρ a q ha) (.app (h.rename ρ) (.refl q))

mutual
  /-- Reifying a syntactically related semantic value produces a term
  convertible to the related term. -/
  theorem quote_syntactic (A : Ty Base) : ∀ {Γ} (v : Sem Γ A) (t : Tm Γ A),
      SyntacticRelated A v t → BetaEtaEq (quote A v).toTm t := by
    intro Γ v t h
    cases A with
    | base b => exact h
    | arr A B =>
      have harg : SyntacticRelated A
          (reflect A (.var (.zero : Var (A :: Γ) A)))
          (.var (.zero : Var (A :: Γ) A)) :=
        by
          simpa using
            (reflect_syntactic A (.var (.zero : Var (A :: Γ) A)))
      have hbody := h (.succ : Ren Γ (A :: Γ))
        (reflect A (.var .zero)) (.var .zero) harg
      exact (BetaEtaEq.lam (quote_syntactic B _ _ hbody)).trans
        (BetaEtaEq.eta t)

  /-- Reflecting a neutral term produces a semantic value syntactically
  related to that neutral term. -/
  theorem reflect_syntactic (A : Ty Base) : ∀ {Γ} (n : Ne Γ A),
      SyntacticRelated A (reflect A n) n.toTm := by
    intro Γ n
    cases A with
    | base b => exact .refl _
    | arr A B =>
      intro Δ ρ a s ha
      have hneutral :
          SyntacticRelated B
            (reflect B (.app (n.rename ρ) (quote A a)))
            (.app (n.rename ρ).toTm (quote A a).toTm) :=
        reflect_syntactic B _
      apply hneutral.congr B
      rw [Ne.toTm_rename]
      exact .app (.refl _) (quote_syntactic A a s ha)
end

/-- A semantic environment is syntactically related to a simultaneous
substitution when corresponding variables are related. -/
def SemEnv.SyntacticallyRelated (ξ : SemEnv Δ Γ) (σ : Sub Γ Δ) : Prop :=
  ∀ {A} (x : Var Γ A), SyntacticRelated A (ξ x) (σ x)

namespace SemEnv.SyntacticallyRelated

/-- Related environments remain related after extension by related values. -/
theorem cons {ξ : SemEnv Δ Γ} {σ : Sub Γ Δ}
    (h : ξ.SyntacticallyRelated σ) {a : Sem Δ A} {s : Tm Δ A}
    (ha : SyntacticRelated A a s) :
    SemEnv.SyntacticallyRelated (SemEnv.cons a ξ) (Sub.cons s σ) := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact h x

/-- Related environments remain related after a common renaming. -/
theorem rename {ξ : SemEnv Δ Γ} {σ : Sub Γ Δ}
    (h : ξ.SyntacticallyRelated σ) (ρ : Ren Δ Θ) :
    SemEnv.SyntacticallyRelated (SemEnv.rename ρ ξ) (Sub.rename σ ρ) := by
  intro A x
  induction A with
  | base b =>
      simp only [SemEnv.rename_apply, Sub.rename_apply, SyntacticRelated,
        Sem.rename]
      exact (BetaEtaEq.of_eq (Ne.toTm_rename ρ
        (show Ne Δ (.base b) from ξ x))).trans ((h x).rename ρ)
  | arr A B ihA ihB =>
      intro Ω τ a s ha
      change SyntacticRelated B ((ξ x) (Var.comp ρ τ) a) _
      have hx := h x (Var.comp ρ τ) a s ha
      apply hx.congr B
      apply BetaEtaEq.of_eq
      simp only [Sub.rename_apply, Tm.rename_comp]

end SemEnv.SyntacticallyRelated

/-- The fundamental theorem of the syntactic logical relation: evaluation in
related semantic and syntactic environments produces related results. -/
theorem nbeEval_syntactic (t : Tm Γ A) (ξ : SemEnv Δ Γ) (σ : Sub Γ Δ)
    (hξ : ξ.SyntacticallyRelated σ) :
    SyntacticRelated A (nbeEval t ξ) (Tm.subst σ t) := by
  induction t generalizing Δ with
  | var x => exact hξ x
  | @app A B Γ f a ihf iha =>
      simpa only [nbeEval_app, Tm.subst_app, Tm.rename_id]
        using ihf ξ σ hξ Var.id (nbeEval a ξ) (Tm.subst σ a) (iha ξ σ hξ)
  | @lam A B Γ body ih =>
      intro Θ ρ a s ha
      simp only [nbeEval_lam_apply]
      have hbody := ih (SemEnv.cons a (SemEnv.rename ρ ξ))
        (Sub.cons s (Sub.rename σ ρ))
        (SemEnv.SyntacticallyRelated.cons
          (SemEnv.SyntacticallyRelated.rename hξ ρ) ha)
      apply hbody.congr B
      rw [Tm.rename_subst]
      rw [Tm.subst_cons]
      exact (BetaEtaEq.beta (Tm.subst (Sub.lift (Sub.rename σ ρ)) body) s).symm

/-- The reflected identity environment is related to the identity syntactic
substitution. -/
theorem identity_syntactic :
    SemEnv.SyntacticallyRelated
      (SemEnv.identity (Base := Base) (Γ := Γ)) Sub.id := by
  intro A x
  exact reflect_syntactic A (.var x)

/-- Every term is beta-eta convertible to the eta-long normal form computed
by normalization by evaluation. -/
theorem betaEtaEq_normalizeTm (t : Tm Γ A) :
    BetaEtaEq t (normalizeTm t) := by
  apply BetaEtaEq.symm
  apply quote_syntactic A
  simpa only [Tm.subst_id] using
    (nbeEval_syntactic t SemEnv.identity Sub.id identity_syntactic)

/-- Equality of NbE normal forms is complete for beta-eta conversion. -/
theorem betaEtaEq_of_normalizeTm_eq {t u : Tm Γ A}
    (h : normalizeTm t = normalizeTm u) : BetaEtaEq t u :=
  (betaEtaEq_normalizeTm t).trans
    ((BetaEtaEq.of_eq h).trans (betaEtaEq_normalizeTm u).symm)

/-- NbE equality and declarative beta-eta conversion coincide. -/
theorem betaEtaEq_iff_normalizeTm_eq {t u : Tm Γ A} :
    BetaEtaEq t u ↔ normalizeTm t = normalizeTm u :=
  ⟨BetaEtaEq.normalizeTm_eq, betaEtaEq_of_normalizeTm_eq⟩

/-- The previously isolated completeness criterion now holds at every
context and type. -/
theorem betaEtaComplete : BetaEtaComplete Base Γ A :=
  fun h => betaEtaEq_of_normalizeTm_eq (NbeEq.iff_normalizeTm_eq.mp h)

end Cslib.Languages.LambdaCalculus.Stlc
