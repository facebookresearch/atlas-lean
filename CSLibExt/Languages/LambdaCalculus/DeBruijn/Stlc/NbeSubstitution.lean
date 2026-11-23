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
# Logical substitution for STLC normalization by evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeNaturality

/-!
# Logical substitution for STLC normalization by evaluation

Raw Kripke functions can inspect non-natural semantic arguments, so equality
of such functions is too strong for a substitution theorem.  This file uses a
type-directed logical relation: functions are compared only on coherent,
related arguments.  Reification observes exactly this relation.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Θ Ω : List (Ty Base)}

namespace Sem

mutual
  /-- Observational equality of semantic values at a simple type. -/
  def Related : (A : Ty Base) → {Γ : List (Ty Base)} → Sem Γ A → Sem Γ A → Prop
    | .base _, _, v, w => v = w
    | A ⇒ B, _, f, g =>
        ∀ {Δ} (ρ : Ren _ Δ) (a b : Sem Δ A),
          Logical A a → Logical A b → Related A a b →
          Related B (f ρ a) (g ρ b)

  /-- Logical semantic values are natural and extensionally preserve the
  logical relation. -/
  def Logical : (A : Ty Base) → {Γ : List (Ty Base)} → Sem Γ A → Prop
    | .base _, _, _ => True
    | A ⇒ B, _, f =>
        Natural (A ⇒ B) f ∧
        ∀ {Δ} (ρ : Ren _ Δ) (a b : Sem Δ A),
          Logical A a → Logical A b → Related A a b →
          Related B (f ρ a) (f ρ b)
end

/-- Every logical value is related to itself. -/
theorem Logical.related_refl {v : Sem Γ A} (hv : Logical A v) : Related A v v := by
  cases A with
  | base => rfl
  | arr => exact hv.2

/-- Logical values are natural. -/
theorem Logical.natural {v : Sem Γ A} (hv : Logical A v) : Natural A v := by
  cases A with
  | base => trivial
  | arr => exact hv.1

/-- Naturality together with self-relatedness reconstructs logicality. -/
theorem Logical.of_natural_related_refl {v : Sem Γ A} (hn : Natural A v)
    (hr : Related A v v) : Logical A v := by
  cases A with
  | base => trivial
  | arr => exact ⟨hn, hr⟩

/-- Logical function application preserves the logical relation. -/
theorem Related.app {f g : Sem Γ (A ⇒ B)} (hfg : Related (A ⇒ B) f g)
    (ρ : Ren Γ Δ) {a b : Sem Δ A} (ha : Logical A a) (hb : Logical A b)
    (hab : Related A a b) : Related B (f ρ a) (g ρ b) :=
  hfg ρ a b ha hb hab

/-- Applying a logical function to a logical argument produces a logical
result. -/
theorem Logical.app {f : Sem Γ (A ⇒ B)} (hf : Logical (A ⇒ B) f)
    (ρ : Ren Γ Δ) {a : Sem Δ A} (ha : Logical A a) : Logical B (f ρ a) :=
  Logical.of_natural_related_refl (hf.natural.app ρ ha.natural)
    (hf.related_refl ρ a a ha ha ha.related_refl)

private theorem related_symm_trans (A : Ty Base) :
    (∀ {Γ} {v w : Sem Γ A}, Related A v w → Related A w v) ∧
    (∀ {Γ} {v w z : Sem Γ A}, Logical A v → Logical A w →
      Logical A z → Related A v w → Related A w z → Related A v z) := by
  induction A with
  | base =>
    constructor
    · intro Γ v w h
      exact Eq.symm h
    · intro Γ v w z hv hw hz hvw hwz
      exact Eq.trans hvw hwz
  | arr A B ihA ihB =>
    constructor
    · intro Γ f g hfg Δ ρ a b ha hb hab
      exact ihB.1 (hfg ρ b a hb ha (ihA.1 hab))
    · intro Γ f g k hf hg hk hfg hgk Δ ρ a c ha hc hac
      have haa : Related A a a := ha.related_refl
      have h₁ := hfg ρ a a ha ha haa
      have h₂ := hgk ρ a c ha hc hac
      exact ihB.2 (Logical.app hf ρ ha) (Logical.app hg ρ ha)
        (Logical.app hk ρ hc) h₁ h₂

theorem Related.symm (A : Ty Base) {v w : Sem Γ A} (h : Related A v w) :
    Related A w v := (related_symm_trans A).1 h

theorem Related.trans (A : Ty Base) {v w z : Sem Γ A} (hv : Logical A v)
    (hw : Logical A w) (hz : Logical A z) (hvw : Related A v w)
    (hwz : Related A w z) : Related A v z :=
  (related_symm_trans A).2 hv hw hz hvw hwz

end Sem

/-- Reflection is logical and reification identifies logically related
values. -/
theorem reflect_logical_quote_related (A : Ty Base) :
    (∀ {Γ} (n : Ne Γ A), Sem.Logical A (reflect A n)) ∧
    (∀ {Γ} {v w : Sem Γ A}, Sem.Related A v w → quote A v = quote A w) := by
  induction A with
  | base b =>
    constructor
    · intro Γ n
      trivial
    · intro Γ v w h
      exact congrArg Nf.base h
  | arr A B ihA ihB =>
    constructor
    · intro Γ n
      constructor
      · exact reflect_natural (A ⇒ B) n
      · intro Δ ρ a b ha hb hab
        have hquote : quote A a = quote A b := ihA.2 hab
        change Sem.Related B
          (reflect B (.app (n.rename ρ) (quote A a)))
          (reflect B (.app (n.rename ρ) (quote A b)))
        rw [hquote]
        exact (ihB.1 _).related_refl
    · intro Γ v w hvw
      simp only [quote]
      apply congrArg Nf.lam
      apply ihB.2
      exact hvw .succ (reflect A (.var .zero)) (reflect A (.var .zero))
        (ihA.1 _) (ihA.1 _) (ihA.1 _).related_refl

/-- Reflected neutral syntax is a logical semantic value. -/
theorem reflect_logical (A : Ty Base) (n : Ne Γ A) :
    Sem.Logical A (reflect A n) := (reflect_logical_quote_related A).1 n

/-- Reification cannot distinguish logically related semantic values. -/
theorem quote_eq_of_related (A : Ty Base) {v w : Sem Γ A}
    (h : Sem.Related A v w) : quote A v = quote A w :=
  (reflect_logical_quote_related A).2 h

/-- Logicality and relatedness are preserved by future-context renaming. -/
theorem logical_rename_related_rename (A : Ty Base) :
    (∀ {Γ Δ} (ρ : Ren Γ Δ) (v : Sem Γ A), Sem.Logical A v →
      Sem.Logical A (Sem.rename ρ A v)) ∧
    (∀ {Γ Δ} (ρ : Ren Γ Δ) {v w : Sem Γ A}, Sem.Related A v w →
      Sem.Related A (Sem.rename ρ A v) (Sem.rename ρ A w)) := by
  induction A with
  | base b =>
    constructor
    · intro Γ Δ ρ v hv
      trivial
    · intro Γ Δ ρ v w hvw
      exact congrArg (Ne.rename ρ) hvw
  | arr A B ihA ihB =>
    constructor
    · intro Γ Δ ρ f hf
      constructor
      · exact hf.natural.rename ρ
      · intro Θ σ a b ha hb hab
        exact hf.related_refl (Var.comp ρ σ) a b ha hb hab
    · intro Γ Δ ρ f g hfg Θ σ a b ha hb hab
      exact hfg (Var.comp ρ σ) a b ha hb hab

theorem Sem.Logical.rename (ρ : Ren Γ Δ) {v : Sem Γ A} (hv : Logical A v) :
    Logical A (Sem.rename ρ A v) := (logical_rename_related_rename A).1 ρ v hv

theorem Sem.Related.rename (ρ : Ren Γ Δ) {v w : Sem Γ A} (h : Related A v w) :
    Related A (Sem.rename ρ A v) (Sem.rename ρ A w) :=
  (logical_rename_related_rename A).2 ρ h

/-- A semantic environment is logical when all of its entries are logical. -/
def SemEnv.Logical (η : SemEnv Δ Γ) : Prop :=
  ∀ {A} (x : Var Γ A), Sem.Logical A (η x)

/-- Pointwise logical relatedness of semantic environments. -/
def SemEnv.Related (ξ ζ : SemEnv Δ Γ) : Prop :=
  ∀ {A} (x : Var Γ A), Sem.Related A (ξ x) (ζ x)

namespace SemEnv

theorem Logical.natural {η : SemEnv Δ Γ} (hη : Logical η) : Natural η :=
  fun x => (hη x).natural

theorem Logical.related_refl {η : SemEnv Δ Γ} (hη : Logical η) : Related η η :=
  fun x => (hη x).related_refl

theorem Logical.rename {η : SemEnv Δ Γ} (hη : Logical η) (ρ : Ren Δ Θ) :
    Logical (SemEnv.rename ρ η) := fun x => (hη x).rename ρ

theorem Related.rename {ξ ζ : SemEnv Δ Γ} (h : Related ξ ζ) (ρ : Ren Δ Θ) :
    Related (SemEnv.rename ρ ξ) (SemEnv.rename ρ ζ) := fun x => (h x).rename ρ

theorem Logical.cons {η : SemEnv Δ Γ} {a : Sem Δ A} (ha : Sem.Logical A a)
    (hη : Logical η) : Logical (SemEnv.cons a η) := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact hη x

theorem Related.cons {ξ ζ : SemEnv Δ Γ} {a b : Sem Δ A}
    (hab : Sem.Related A a b) (h : Related ξ ζ) :
    Related (SemEnv.cons a ξ) (SemEnv.cons b ζ) := by
  intro C x
  cases x with
  | zero => exact hab
  | succ x => exact h x

theorem logical_identity : @Logical Base Γ Γ SemEnv.identity :=
  fun x => reflect_logical _ (.var x)

end SemEnv

/-- Fundamental theorem for the logical NbE semantics: evaluation maps
logical environments to logical values and related environments to related
values. -/
theorem nbeEval_logical_related (t : Tm Γ A) :
    (∀ {Δ} (η : SemEnv Δ Γ), η.Logical → Sem.Logical A (nbeEval t η)) ∧
    (∀ {Δ} (ξ ζ : SemEnv Δ Γ), ξ.Logical → ζ.Logical → ξ.Related ζ →
      Sem.Related A (nbeEval t ξ) (nbeEval t ζ)) := by
  induction t with
  | var x =>
    constructor
    · intro Δ η hη
      exact hη x
    · intro Δ ξ ζ hξ hζ h
      exact h x
  | @app A B Γ f a ihf iha =>
    constructor
    · intro Δ η hη
      exact (ihf.1 η hη).app Var.id (iha.1 η hη)
    · intro Δ ξ ζ hξ hζ h
      exact ihf.2 ξ ζ hξ hζ h Var.id _ _
        (iha.1 ξ hξ) (iha.1 ζ hζ) (iha.2 ξ ζ hξ hζ h)
  | @lam A B Γ body ih =>
    constructor
    · intro Δ η hη
      apply Sem.Logical.of_natural_related_refl
      · exact nbeEval_natural (.lam body) η hη.natural
      · intro Θ ρ a b ha hb hab
        simp only [nbeEval_lam_apply]
        exact ih.2 _ _
          (SemEnv.Logical.cons ha (hη.rename ρ))
          (SemEnv.Logical.cons hb (hη.rename ρ))
          (SemEnv.Related.cons hab
            (SemEnv.Related.rename hη.related_refl ρ))
    · intro Δ ξ ζ hξ hζ h Θ ρ a b ha hb hab
      simp only [nbeEval_lam_apply]
      exact ih.2 _ _
        (SemEnv.Logical.cons ha (hξ.rename ρ))
        (SemEnv.Logical.cons hb (hζ.rename ρ))
        (SemEnv.Related.cons hab (SemEnv.Related.rename h ρ))

theorem nbeEval_logical (t : Tm Γ A) (η : SemEnv Δ Γ) (hη : η.Logical) :
    Sem.Logical A (nbeEval t η) := (nbeEval_logical_related t).1 η hη

theorem nbeEval_logically_related (t : Tm Γ A) (ξ ζ : SemEnv Δ Γ)
    (hξ : ξ.Logical) (hζ : ζ.Logical) (h : ξ.Related ζ) :
    Sem.Related A (nbeEval t ξ) (nbeEval t ζ) :=
  (nbeEval_logical_related t).2 ξ ζ hξ hζ h

namespace SemEnv

theorem Logical.evalSub {η : SemEnv Θ Δ} (hη : Logical η) (σ : Sub Γ Δ) :
    Logical (evalSub σ η) := fun x => nbeEval_logical (σ x) η hη

/-- The semantic environment obtained from a lifted substitution is related
to extension of the original semantic substitution environment. -/
theorem evalSub_lift_related (σ : Sub Γ Δ) (η : SemEnv Θ Δ)
    (hη : Logical η) (ρ : Ren Θ Ω) {a b : Sem Ω A}
    (hab : Sem.Related A a b) :
    Related
      (evalSub (Sub.lift σ) (SemEnv.cons a (SemEnv.rename ρ η)))
      (SemEnv.cons b (SemEnv.rename ρ (evalSub σ η))) := by
  intro C x
  cases x with
  | zero => exact hab
  | succ x =>
    simp only [evalSub_apply, Sub.lift_succ, Tm.weaken, cons_succ, rename_apply]
    rw [nbeEval_rename_source]
    have hrename := nbeEval_rename_sem (σ x) η hη.natural ρ
    rw [hrename]
    have heq :
        nbeEval (σ x)
            (compRen (SemEnv.cons a (SemEnv.rename ρ η))
              (.succ : Ren Δ (A :: Δ))) =
          nbeEval (σ x) (SemEnv.rename ρ η) := by
      apply nbeEval_congr
      intro D y
      rfl
    rw [heq]
    exact (nbeEval_logical (σ x) (SemEnv.rename ρ η) (hη.rename ρ)).related_refl

end SemEnv

/-- Substituting syntax and evaluating it is logically related to evaluating
the source under the semantic interpretation of the substitution. -/
theorem nbeEval_subst_related (t : Tm Γ A) (σ : Sub Γ Δ)
    (η : SemEnv Θ Δ) (hη : η.Logical) :
    Sem.Related A (nbeEval (Tm.subst σ t) η)
      (nbeEval t (SemEnv.evalSub σ η)) := by
  induction t generalizing Δ Θ with
  | var x => exact (nbeEval_logical (σ x) η hη).related_refl
  | @app A B Γ f a ihf iha =>
    simp only [Tm.subst_app, nbeEval_app]
    exact ihf σ η hη Var.id _ _
      (nbeEval_logical (Tm.subst σ a) η hη)
      (nbeEval_logical a (SemEnv.evalSub σ η) (hη.evalSub σ))
      (iha σ η hη)
  | @lam A B Γ body ih =>
    intro Ω ρ a b ha hb hab
    simp only [Tm.subst_lam, nbeEval_lam_apply]
    let ξ : SemEnv Ω (A :: Δ) := SemEnv.cons a (SemEnv.rename ρ η)
    let ζ : SemEnv Ω (A :: Γ) := SemEnv.evalSub (Sub.lift σ) ξ
    let υ : SemEnv Ω (A :: Γ) :=
      SemEnv.cons b (SemEnv.rename ρ (SemEnv.evalSub σ η))
    have hξ : ξ.Logical := SemEnv.Logical.cons ha (hη.rename ρ)
    have hζ : ζ.Logical := hξ.evalSub (Sub.lift σ)
    have hυ : υ.Logical := SemEnv.Logical.cons hb
      (SemEnv.Logical.rename (SemEnv.Logical.evalSub hη σ) ρ)
    have h₁ : Sem.Related B (nbeEval (Tm.subst (Sub.lift σ) body) ξ)
        (nbeEval body ζ) := ih (Sub.lift σ) ξ hξ
    have henv : ζ.Related υ :=
      SemEnv.evalSub_lift_related σ η hη ρ hab
    have h₂ : Sem.Related B (nbeEval body ζ) (nbeEval body υ) :=
      nbeEval_logically_related body ζ υ hζ hυ henv
    exact Sem.Related.trans B
      (nbeEval_logical (Tm.subst (Sub.lift σ) body) ξ hξ)
      (nbeEval_logical body ζ hζ) (nbeEval_logical body υ hυ) h₁ h₂

/-- Normalization after syntactic substitution agrees with reifying the source
in the semantic environment obtained by evaluating the substitution. -/
theorem normalizeNf_subst (t : Tm Γ A) (σ : Sub Γ Δ) :
    normalizeNf (Tm.subst σ t) =
      quote A (nbeEval t (SemEnv.evalSub σ SemEnv.identity)) := by
  simp only [normalizeNf]
  apply quote_eq_of_related A
  exact nbeEval_subst_related t σ SemEnv.identity SemEnv.logical_identity

/-- The term-level canonical representative after substitution is obtained by
erasing the reified semantic substitution result. -/
theorem normalizeTm_subst (t : Tm Γ A) (σ : Sub Γ Δ) :
    normalizeTm (Tm.subst σ t) =
      (quote A (nbeEval t (SemEnv.evalSub σ SemEnv.identity))).toTm := by
  exact congrArg Nf.toTm (normalizeNf_subst t σ)

/-- The single-substitution instance of logical substitution gives a direct
normal-form account of beta instantiation. -/
theorem normalizeNf_instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    normalizeNf (Tm.instantiate body a) =
      quote B
        (nbeEval body (SemEnv.evalSub (Sub.single a) SemEnv.identity)) := by
  exact normalizeNf_subst body (Sub.single a)

/-- The corresponding term-level statement for beta instantiation. -/
theorem normalizeTm_instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    normalizeTm (Tm.instantiate body a) =
      (quote B
        (nbeEval body (SemEnv.evalSub (Sub.single a) SemEnv.identity))).toTm := by
  exact normalizeTm_subst body (Sub.single a)

end Cslib.Languages.LambdaCalculus.Stlc
