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
# Naturality and substitution laws for STLC normalization by evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeEquivalence

/-!
# Naturality and substitution laws for STLC normalization by evaluation

The raw Kripke function space used by the NbE semantics contains functions
that need not commute with future-context renaming.  This file isolates the
coherent semantic values, proves that reflection and evaluation produce them,
and derives renaming and simultaneous-substitution laws for the evaluator.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Θ Ω : List (Ty Base)}

namespace Sem

/-- A semantic value is natural when semantic functions preserve natural
arguments and commute with every future-context renaming. -/
def Natural : (A : Ty Base) → {Γ : List (Ty Base)} → Sem Γ A → Prop
  | .base _, _, _ => True
  | A ⇒ B, _, f =>
      (∀ {Δ} (ρ : Ren _ Δ) (a : Sem Δ A), Natural A a → Natural B (f ρ a)) ∧
      (∀ {Δ Θ} (ρ : Ren _ Δ) (σ : Ren Δ Θ) (a : Sem Δ A), Natural A a →
        rename σ B (f ρ a) = f (Var.comp ρ σ) (rename σ A a))

theorem Natural.app {f : Sem Γ (A ⇒ B)} (hf : Natural (A ⇒ B) f)
    (ρ : Ren Γ Δ) {a : Sem Δ A} (ha : Natural A a) : Natural B (f ρ a) :=
  hf.1 ρ a ha

theorem Natural.comm {f : Sem Γ (A ⇒ B)} (hf : Natural (A ⇒ B) f)
    (ρ : Ren Γ Δ) (σ : Ren Δ Θ) {a : Sem Δ A} (ha : Natural A a) :
    rename σ B (f ρ a) = f (Var.comp ρ σ) (rename σ A a) :=
  hf.2 ρ σ a ha

/-- Renaming a natural semantic value preserves naturality. -/
theorem Natural.rename (ρ : Ren Γ Δ) {v : Sem Γ A} (hv : Natural A v) :
    Natural A (rename ρ A v) := by
  induction A generalizing Γ Δ with
  | base => trivial
  | arr A B ihA ihB =>
    constructor
    · intro Θ σ a ha
      exact hv.app (Var.comp ρ σ) ha
    · intro Θ Ω σ τ a ha
      change rename τ B (v (Var.comp ρ σ) a) =
        v (Var.comp ρ (Var.comp σ τ)) (rename τ A a)
      exact hv.comm (Var.comp ρ σ) τ ha

end Sem

/-- A semantic environment is natural when each value it assigns is natural. -/
def SemEnv.Natural (η : SemEnv Δ Γ) : Prop :=
  ∀ {A} (x : Var Γ A), Sem.Natural A (η x)

/-- Reflection always produces a natural value, while reification commutes
with renaming on natural values. -/
theorem reflect_natural_quote_rename (A : Ty Base) :
    (∀ {Γ} (n : Ne Γ A), Sem.Natural A (reflect A n)) ∧
    (∀ {Γ Δ} (ρ : Ren Γ Δ) (v : Sem Γ A), Sem.Natural A v →
      (quote A v).rename ρ = quote A (Sem.rename ρ A v)) := by
  induction A with
  | base b =>
    constructor
    · intro Γ n
      trivial
    · intro Γ Δ ρ v hv
      rfl
  | arr A B ihA ihB =>
    constructor
    · intro Γ n
      constructor
      · intro Δ ρ a ha
        exact ihB.1 _
      · intro Δ Θ ρ σ a ha
        change Sem.rename σ B
            (reflect B (.app (n.rename ρ) (quote A a))) =
          reflect B (.app (n.rename (Var.comp ρ σ))
            (quote A (Sem.rename σ A a)))
        rw [reflect_rename]
        apply congrArg (reflect B)
        simp only [Ne.rename]
        rw [Ne.rename_comp, ihA.2 σ a ha]
    · intro Γ Δ ρ f hf
      simp only [quote, Nf.rename]
      apply congrArg Nf.lam
      rw [ihB.2 (Var.lift ρ) _ (hf.app .succ (ihA.1 (.var .zero)))]
      rw [hf.comm .succ (Var.lift ρ) (ihA.1 (.var .zero))]
      congr 2
      simpa using reflect_rename A (Var.lift ρ) (.var .zero)

/-- Reflected neutrals are coherent Kripke values. -/
theorem reflect_natural (A : Ty Base) (n : Ne Γ A) :
    Sem.Natural A (reflect A n) := (reflect_natural_quote_rename A).1 n

/-- Reification of a natural value commutes with renaming. -/
theorem quote_rename (A : Ty Base) (ρ : Ren Γ Δ) (v : Sem Γ A)
    (hv : Sem.Natural A v) :
    (quote A v).rename ρ = quote A (Sem.rename ρ A v) :=
  (reflect_natural_quote_rename A).2 ρ v hv

namespace SemEnv

variable {η : SemEnv Θ Δ}

variable {η : SemEnv Δ Γ}

/-- Pointwise renaming preserves a natural semantic environment. -/
theorem Natural.rename (hη : Natural η) (ρ : Ren Δ Θ) :
    Natural (SemEnv.rename ρ η) := fun x => (hη x).rename ρ

/-- Extending a natural environment with a natural value preserves
naturality. -/
theorem Natural.cons {a : Sem Δ A} (ha : Sem.Natural A a)
    (hη : Natural η) : Natural (SemEnv.cons a η) := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact hη x

/-- The identity semantic environment is natural. -/
theorem natural_identity : @Natural Base Γ Γ SemEnv.identity :=
  fun x => reflect_natural _ (.var x)

end SemEnv

/-- Evaluation preserves naturality and commutes with transport to every
future context.  The two statements are proved together because the function
case uses transport coherence to establish naturality under application. -/
theorem nbeEval_natural_rename (t : Tm Γ A) :
    (∀ {Δ} (η : SemEnv Δ Γ), η.Natural → Sem.Natural A (nbeEval t η)) ∧
    (∀ {Δ Θ} (η : SemEnv Δ Γ), η.Natural → (ρ : Ren Δ Θ) →
      Sem.rename ρ A (nbeEval t η) = nbeEval t (SemEnv.rename ρ η)) := by
  induction t with
  | var x =>
    constructor
    · intro Δ η hη
      exact hη x
    · intro Δ Θ η hη ρ
      rfl
  | @app A B Γ f a ihf iha =>
    constructor
    · intro Δ η hη
      exact (ihf.1 η hη).app Var.id (iha.1 η hη)
    · intro Δ Θ η hη ρ
      simp only [nbeEval_app]
      rw [← ihf.2 η hη ρ, ← iha.2 η hη ρ]
      exact (ihf.1 η hη).comm Var.id ρ (iha.1 η hη)
  | @lam A B Γ body ih =>
    constructor
    · intro Δ η hη
      constructor
      · intro Θ ρ a ha
        exact ih.1 _ (SemEnv.Natural.cons ha (hη.rename ρ))
      · intro Θ Ω ρ σ a ha
        simp only [nbeEval_lam_apply]
        rw [ih.2 _ (SemEnv.Natural.cons ha (hη.rename ρ)) σ]
        apply nbeEval_congr
        intro C x
        cases x with
        | zero => rfl
        | succ x =>
          simp only [SemEnv.rename_apply, SemEnv.cons_succ]
          exact Sem.rename_comp ρ σ C (η x)
    · intro Δ Θ η hη ρ
      funext Ω σ a
      simp only [Sem.rename_arr_apply, nbeEval_lam_apply]
      apply nbeEval_congr
      intro C x
      cases x with
      | zero => rfl
      | succ x =>
        simp only [SemEnv.cons_succ, SemEnv.rename_apply]
        exact (Sem.rename_comp ρ σ C (η x)).symm

/-- Evaluation of a term in a natural environment is a natural semantic
value. -/
theorem nbeEval_natural (t : Tm Γ A) (η : SemEnv Δ Γ) (hη : η.Natural) :
    Sem.Natural A (nbeEval t η) := (nbeEval_natural_rename t).1 η hη

/-- Evaluation commutes with future-context renaming for natural
environments. -/
theorem nbeEval_rename_sem (t : Tm Γ A) (η : SemEnv Δ Γ) (hη : η.Natural)
    (ρ : Ren Δ Θ) :
    Sem.rename ρ A (nbeEval t η) = nbeEval t (SemEnv.rename ρ η) :=
  (nbeEval_natural_rename t).2 η hη ρ

namespace SemEnv

/-- Precompose a semantic environment with a source-context renaming. -/
def compRen (η : SemEnv Θ Δ) (ρ : Ren Γ Δ) : SemEnv Θ Γ :=
  fun x => η (ρ x)

@[simp] theorem compRen_apply (η : SemEnv Θ Δ) (ρ : Ren Γ Δ) (x : Var Γ A) :
    compRen η ρ x = η (ρ x) := rfl

theorem Natural.compRen {η : SemEnv Θ Δ} (hη : Natural η) (ρ : Ren Γ Δ) :
    Natural (compRen η ρ) := fun x => hη (ρ x)

end SemEnv

/-- Evaluation commutes with renaming the free variables of source syntax. -/
theorem nbeEval_rename_source (t : Tm Γ A) (ρ : Ren Γ Δ) (η : SemEnv Θ Δ) :
    nbeEval (Tm.rename ρ t) η = nbeEval t (SemEnv.compRen η ρ) := by
  induction t generalizing Δ Θ with
  | var x => rfl
  | app f a ihf iha => simp only [Tm.rename_app, nbeEval_app, ihf, iha]
  | @lam A B Γ body ih =>
    funext Ω σ a
    simp only [Tm.rename_lam, nbeEval_lam_apply]
    rw [ih]
    apply nbeEval_congr
    intro C x
    cases x with
    | zero => rfl
    | succ x => rfl

namespace SemEnv

variable {η : SemEnv Θ Δ}

/-- Evaluate every term in a simultaneous substitution to obtain a semantic
environment. -/
def evalSub (σ : Sub Γ Δ) (η : SemEnv Θ Δ) : SemEnv Θ Γ :=
  fun x => nbeEval (σ x) η

@[simp] theorem evalSub_apply (σ : Sub Γ Δ) (η : SemEnv Θ Δ) (x : Var Γ A) :
    evalSub σ η x = nbeEval (σ x) η := rfl

theorem Natural.evalSub (hη : Natural η) (σ : Sub Γ Δ) :
    Natural (evalSub σ η) := fun x => nbeEval_natural (σ x) η hη

/-- Evaluating a substitution induced by a renaming only precomposes the
environment. -/
theorem evalSub_ofRen (ρ : Ren Γ Δ) (η : SemEnv Θ Δ) :
    @evalSub Base Γ Δ Θ (Sub.ofRen ρ) η =
      @compRen Base Γ Δ Θ η ρ := by
  funext A x
  rfl

/-- Evaluating the identity substitution leaves the semantic environment
unchanged. -/
theorem evalSub_id (η : SemEnv Θ Γ) :
    @evalSub Base Γ Γ Θ Sub.id η = @η := by
  funext A x
  rfl

/-- Renaming every substitution image before evaluation is equivalent to
precomposing the target environment by that renaming. -/
theorem evalSub_rename_images (σ : Sub Γ Δ) (ρ : Ren Δ Θ)
    (η : SemEnv Ω Θ) :
    @evalSub Base Γ Θ Ω (fun x => Tm.rename ρ (σ x)) η =
      @evalSub Base Γ Δ Ω σ (@compRen Base Δ Θ Ω η ρ) := by
  funext A x
  exact nbeEval_rename_source (σ x) ρ η

/-- Evaluating substitution images commutes with future-context renaming. -/
theorem rename_evalSub (σ : Sub Γ Δ) (η : SemEnv Θ Δ) (hη : Natural η)
    (ρ : Ren Θ Ω) :
    @SemEnv.rename Base Γ Θ Ω ρ (@evalSub Base Γ Δ Θ σ η) =
      @evalSub Base Γ Δ Ω σ (@SemEnv.rename Base Δ Θ Ω ρ η) := by
  funext A x
  exact nbeEval_rename_sem (σ x) η hη ρ

/-- Renaming the identity environment is the identity environment
precomposed with the same source renaming. -/
theorem rename_identity_eq_compRen (ρ : Ren Γ Δ) :
    @SemEnv.rename Base Γ Γ Δ ρ SemEnv.identity =
      @compRen Base Γ Δ Δ (@SemEnv.identity Base Δ) ρ := by
  funext A x
  exact reflect_rename A ρ (.var x)

/-- Precomposition by source renamings is associative. -/
theorem compRen_comp (η : SemEnv Ω Θ) (ρ : Ren Δ Θ) (σ : Ren Γ Δ) :
    @compRen Base Γ Δ Ω (@compRen Base Δ Θ Ω η ρ) σ =
      @compRen Base Γ Θ Ω η (Var.comp σ ρ) := by
  funext A x
  rfl

/-- Precomposition by the identity renaming is inert. -/
theorem compRen_id (η : SemEnv Θ Γ) :
    @compRen Base Γ Γ Θ η Var.id = @η := by
  funext A x
  rfl

end SemEnv

/-- NbE normalization commutes with renaming free variables. -/
theorem normalizeNf_rename (t : Tm Γ A) (ρ : Ren Γ Δ) :
    normalizeNf (Tm.rename ρ t) = (normalizeNf t).rename ρ := by
  simp only [normalizeNf, nbeEval_rename_source]
  rw [← SemEnv.rename_identity_eq_compRen ρ]
  rw [← nbeEval_rename_sem t SemEnv.identity SemEnv.natural_identity ρ]
  exact (quote_rename A ρ (nbeEval t SemEnv.identity)
    (nbeEval_natural t SemEnv.identity SemEnv.natural_identity)).symm

/-- The erased canonical representative also commutes with renaming. -/
theorem normalizeTm_rename (t : Tm Γ A) (ρ : Ren Γ Δ) :
    normalizeTm (Tm.rename ρ t) = Tm.rename ρ (normalizeTm t) := by
  simp only [normalizeTm, normalizeNf_rename, Nf.toTm_rename]

/-- NbE equality is stable under source-context renaming. -/
theorem NbeEq.rename {t u : Tm Γ A} (h : NbeEq t u) (ρ : Ren Γ Δ) :
    NbeEq (Tm.rename ρ t) (Tm.rename ρ u) := by
  unfold NbeEq at h ⊢
  rw [normalizeNf_rename, normalizeNf_rename, h]

/-- Renaming a canonical representative gives the canonical representative of
the renamed source term. -/
theorem CanonicalTm.rename (t : CanonicalTm Γ A) (ρ : Ren Γ Δ) :
    normalizeTm (Tm.rename ρ t.1) = Tm.rename ρ t.1 := by
  rw [normalizeTm_rename, t.2]

/-- Normalization after two source renamings agrees with normalization after
their composite. -/
theorem normalizeTm_rename_comp (t : Tm Γ A) (ρ : Ren Γ Δ) (σ : Ren Δ Θ) :
    normalizeTm (Tm.rename σ (Tm.rename ρ t)) =
      Tm.rename (Var.comp ρ σ) (normalizeTm t) := by
  rw [normalizeTm_rename, normalizeTm_rename, Tm.rename_comp]

end Cslib.Languages.LambdaCalculus.Stlc
