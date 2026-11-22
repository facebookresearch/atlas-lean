/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Correctness of normalization by evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Contextual
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeEvaluation

/-!
# Correctness of normalization by evaluation

The Kripke NbE semantics is connected to every set-theoretic model by a
logical relation.  Reflection and reification satisfy this relation, and the
fundamental lemma shows that NbE evaluation agrees with ordinary denotation.
Consequently every term is model-equal to its reified normal form.  Equality
of computed normal forms is therefore a sound test for model equality; no
converse or canonicity claim is made here.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u v

variable {Base : Type u}
variable {I : Base → Type v}
variable {A B : Ty Base}
variable {Γ Δ Θ : List (Ty Base)}
variable {η : Env I Γ} {v : Sem Γ A} {d : Ty.denote I A}

/-- A Kripke semantic value realizes a set-theoretic denotation when base
neutrals have that denotation and functions preserve realization after every
future-context renaming. -/
def NbeRelated (I : Base → Type v) : {Γ : List (Ty Base)} →
    Env I Γ → (A : Ty Base) → Sem Γ A → Ty.denote I A → Prop
  | _, η, .base _, n, d => Tm.denote I n.toTm (@η) = d
  | Γ, η, A ⇒ B, f, d => ∀ {Δ} (ρ : Ren Γ Δ) (θ : Env I Δ),
      @Env.rename Base Γ Δ I ρ θ = @η → ∀ (a : Sem Δ A) (da : Ty.denote I A),
      NbeRelated I (@θ) A a da → NbeRelated I (@θ) B (f ρ a) (d da)

@[simp] theorem nbeRelated_base {b : Base} (η : Env I Γ)
    (n : Sem Γ (.base b)) (d : I b) :
    NbeRelated I (@η) (.base b) n d ↔ Tm.denote I n.toTm (@η) = d := Iff.rfl

@[simp] theorem nbeRelated_arr (η : Env I Γ) (f : Sem Γ (A ⇒ B))
    (d : Ty.denote I (A ⇒ B)) :
    NbeRelated I (@η) (A ⇒ B) f d ↔ ∀ {Δ} (ρ : Ren Γ Δ) (θ : Env I Δ),
      @Env.rename Base Γ Δ I ρ θ = @η → ∀ (a : Sem Δ A) (da : Ty.denote I A),
      NbeRelated I (@θ) A a da → NbeRelated I (@θ) B (f ρ a) (d da) := Iff.rfl

mutual
  /-- Reification preserves the denotation represented by a semantic value. -/
  theorem quote_denote (A : Ty Base) : ∀ {Γ} (η : Env I Γ) (v : Sem Γ A)
      (d : Ty.denote I A), NbeRelated I (@η) A v d →
      Tm.denote I (quote A v).toTm (@η) = d := by
    intro Γ η v d h
    cases A with
    | base => exact h
    | arr A B =>
      simp only [quote, Nf.toTm_lam, Tm.denote_lam]
      funext da
      apply quote_denote (Γ := A :: Γ) B (Env.cons da η)
      apply h .succ (Env.cons da η)
      · funext C x
        rfl
      · exact reflect_related A (Env.cons da η) (.var .zero)

  /-- Reflection represents the denotation of the reflected neutral term. -/
  theorem reflect_related (A : Ty Base) : ∀ {Γ} (η : Env I Γ) (n : Ne Γ A),
      NbeRelated I (@η) A (reflect A n) (Tm.denote I n.toTm (@η)) := by
    intro Γ η n
    cases A with
    | base => rfl
    | arr A B =>
      change ∀ {Δ} (ρ : Ren Γ Δ) (θ : Env I Δ), _
      intro Δ ρ θ hθ a da ha
      change NbeRelated I (@θ) B
        (reflect B (.app (n.rename ρ) (quote A a))) (Tm.denote I n.toTm η da)
      have hr := reflect_related (Γ := Δ) B θ (.app (n.rename ρ) (quote A a))
      have heq : Tm.denote I (Ne.app (n.rename ρ) (quote A a)).toTm θ =
          Tm.denote I n.toTm η da := by
        simp only [Ne.toTm_app, Tm.denote_app]
        rw [Ne.toTm_rename, Tm.denote_rename, hθ, quote_denote A θ a da ha]
      rw [← heq]
      exact hr
end

/-- Realization is stable under transport to a future context. -/
theorem NbeRelated.rename (h : NbeRelated I (@η) A v d) (ρ : Ren Γ Δ)
    (θ : Env I Δ) (hθ : @Env.rename Base Γ Δ I ρ θ = @η) :
    NbeRelated I (@θ) A (Sem.rename ρ A v) d := by
  induction A generalizing Γ Δ with
  | base b =>
    change Ne Γ (.base b) at v
    change Tm.denote I v.toTm (@η) = d at h
    change Tm.denote I (Ne.rename ρ v).toTm (@θ) = d
    rw [Ne.toTm_rename, Tm.denote_rename]
    rw [hθ]
    exact h
  | arr A B ihA ihB =>
    change ∀ {Θ} (σ : Ren Δ Θ) (υ : Env I Θ), _
    intro Θ σ υ hυ a da ha
    apply h (Var.comp ρ σ) υ
    · rw [← hθ]
      funext C x
      exact congrArg (fun e : Env I Δ => e (ρ x)) hυ
    · exact ha

/-- Pointwise realization of a Kripke environment and a denotational
environment. -/
def NbeEnvRelated (I : Base → Type v) (θ : Env I Δ)
    (ξ : SemEnv Δ Γ) (η : Env I Γ) : Prop :=
  ∀ {A} (x : Var Γ A), NbeRelated I (@θ) A (ξ x) (η x)

/-- The fundamental lemma for NbE evaluation. -/
theorem nbeEval_related (t : Tm Γ A) (ξ : SemEnv Δ Γ)
    (η : Env I Γ) (θ : Env I Δ) (hξ : NbeEnvRelated I θ ξ η) :
    NbeRelated I (@θ) A (nbeEval t ξ) (Tm.denote I t (@η)) := by
  induction t generalizing Δ with
  | var x => exact hξ x
  | @app A B Γ f a ihf iha =>
    have hf : NbeRelated I (@θ) (A ⇒ B) (nbeEval f ξ) (Tm.denote I f η) :=
      ihf ξ η θ hξ
    change ∀ {Ω} (ρ : Ren Δ Ω) (υ : Env I Ω), _ at hf
    exact hf Var.id θ rfl (nbeEval a ξ) (Tm.denote I a η) (iha ξ η θ hξ)
  | @lam A B Γ body ih =>
    change ∀ {Ω} (ρ : Ren Δ Ω) (υ : Env I Ω), _
    intro Ω ρ υ hυ a da ha
    apply ih (SemEnv.cons a (SemEnv.rename ρ ξ))
      (Env.cons da η) υ
    intro C x
    cases x with
    | zero => exact ha
    | succ x =>
      exact (hξ x).rename ρ υ hυ

/-- The identity Kripke environment realizes every denotational environment. -/
theorem identity_related (η : Env I Γ) :
    NbeEnvRelated I η SemEnv.identity η := by
  intro A x
  exact reflect_related A η (.var x)

/-- NbE normalization preserves denotation in every set-theoretic model. -/
theorem normalizeTm_denote (I : Base → Type v) (t : Tm Γ A) (η : Env I Γ) :
    Tm.denote I (normalizeTm t) η = Tm.denote I t η := by
  apply quote_denote A η
  exact nbeEval_related t SemEnv.identity η η (identity_related η)

/-- Every term is semantically equal to its NbE result in a fixed model. -/
theorem normalizeTm_semEq (I : Base → Type v) (t : Tm Γ A) :
    SemEq I t (normalizeTm t) := fun η => (normalizeTm_denote I t η).symm

/-- Every term is model-equal to its NbE result. -/
theorem normalizeTm_modelEq (t : Tm Γ A) : ModelEq t (normalizeTm t) :=
  fun I => normalizeTm_semEq I t

/-- Equality of computed normal forms is a sound certificate of model
equality. -/
theorem modelEq_of_normalizeTm_eq {t u : Tm Γ A}
    (h : normalizeTm t = normalizeTm u) : ModelEq t u :=
  ModelEq.trans (normalizeTm_modelEq t)
    (ModelEq.trans (h ▸ ModelEq.refl (normalizeTm t))
      (ModelEq.symm (normalizeTm_modelEq u)))

end Cslib.Languages.LambdaCalculus.Stlc
