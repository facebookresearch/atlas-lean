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
# Canonicality laws for STLC normalization by evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeEvaluation

/-!
# Canonicality laws for STLC normalization by evaluation

This file proves that the evaluator and reifier preserve the normal-form
syntax introduced by the NbE foundation.  In particular, eta-long normal forms
are fixed points of normalization and normalization is idempotent.  These are
computational canonicality properties; they do not assert the converse of
model-equality soundness.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ Δ : List (Ty Base)}

/-- Reflection commutes with transport to a future context. -/
theorem reflect_rename (A : Ty Base) (ρ : Ren Γ Δ) (n : Ne Γ A) :
    Sem.rename ρ A (reflect A n) = reflect A (n.rename ρ) := by
  induction A with
  | base => rfl
  | arr A B ihA ihB =>
    funext Θ σ a
    change reflect B (.app (n.rename (Var.comp ρ σ)) (quote A a)) =
      reflect B (.app ((n.rename ρ).rename σ) (quote A a))
    rw [Ne.rename_comp]

/-- Extending the renamed identity environment with the reflected newest
variable gives the identity environment under a binder. -/
theorem SemEnv.cons_reflect_rename_identity :
    @SemEnv.cons Base A Γ (A :: Γ) (reflect A (.var .zero))
        (SemEnv.rename (.succ : Ren Γ (A :: Γ)) SemEnv.identity) =
      @SemEnv.identity Base (A :: Γ) := by
  funext B x
  cases x with
  | zero => rfl
  | succ x =>
    simp only [SemEnv.cons_succ, SemEnv.rename_apply, SemEnv.identity]
    exact reflect_rename B .succ (.var x)

/-- Evaluation depends only on the pointwise values of its semantic
environment. -/
theorem nbeEval_congr (t : Tm Γ A) {ξ ζ : SemEnv Δ Γ}
    (h : ∀ {B} (x : Var Γ B), ξ x = ζ x) : nbeEval t ξ = nbeEval t ζ := by
  induction t generalizing Δ with
  | var x => exact h x
  | app f a ihf iha => simp only [nbeEval_app, ihf h, iha h]
  | @lam A B Γ body ih =>
    funext Θ ρ a
    simp only [nbeEval_lam_apply]
    apply ih
    intro C x
    cases x with
    | zero => rfl
    | succ x =>
      simp only [SemEnv.cons_succ, SemEnv.rename_apply]
      rw [h x]

/-- Evaluation of neutral syntax in the identity environment agrees with
reflection. -/
theorem nbeEval_ne_toTm (n : Ne Γ A) :
    nbeEval n.toTm SemEnv.identity = reflect A n := by
  exact Ne.rec
    (motive_1 := fun {Γ A} n => nbeEval n.toTm SemEnv.identity = reflect A n)
    (motive_2 := fun {Γ A} n => normalizeNf n.toTm = n)
    (fun _ => rfl)
    (fun f a ihf iha => by
      simp only [Ne.toTm_app, nbeEval_app, ihf, reflect]
      rw [Ne.rename_id]
      change reflect _ (.app f (normalizeNf a.toTm)) = _
      rw [iha])
    (fun n ih => by
      simp only [Nf.toTm_base, normalizeNf, ih, quote, reflect])
    (fun body ih => by
      simp only [Nf.toTm_lam, normalizeNf, nbeEval_lam_apply, quote]
      apply congrArg Nf.lam
      rw [nbeEval_congr body.toTm (fun {C} x =>
        congrFun (congrFun SemEnv.cons_reflect_rename_identity C) x)]
      exact ih)
    n

/-- Eta-long normal forms are fixed points of NbE normalization. -/
@[simp] theorem normalizeNf_toTm (n : Nf Γ A) : normalizeNf n.toTm = n := by
  exact Nf.rec
    (motive_1 := fun {Γ A} n => nbeEval n.toTm SemEnv.identity = reflect A n)
    (motive_2 := fun {Γ A} n => normalizeNf n.toTm = n)
    (fun _ => rfl)
    (fun f a ihf iha => by
      simp only [Ne.toTm_app, nbeEval_app, ihf, reflect]
      rw [Ne.rename_id]
      change reflect _ (.app f (normalizeNf a.toTm)) = _
      rw [iha])
    (fun n ih => by
      simp only [Nf.toTm_base, normalizeNf, ih, quote, reflect])
    (fun body ih => by
      simp only [Nf.toTm_lam, normalizeNf, nbeEval_lam_apply, quote]
      apply congrArg Nf.lam
      rw [nbeEval_congr body.toTm (fun {C} x =>
        congrFun (congrFun SemEnv.cons_reflect_rename_identity C) x)]
      exact ih)
    n

/-- Normalizing the term underlying a computed normal form changes nothing. -/
@[simp] theorem normalizeTm_normalizeNf (t : Tm Γ A) :
    normalizeTm (normalizeNf t).toTm = normalizeTm t := by
  simp only [normalizeTm, normalizeNf_toTm]

/-- NbE normalization is idempotent. -/
@[simp] theorem normalizeTm_idem (t : Tm Γ A) :
    normalizeTm (normalizeTm t) = normalizeTm t := by
  exact normalizeTm_normalizeNf t

/-- A term already presented by an eta-long normal form normalizes to itself. -/
@[simp] theorem normalizeTm_toTm (n : Nf Γ A) : normalizeTm n.toTm = n.toTm := by
  simp only [normalizeTm, normalizeNf_toTm]

/-- The erasure from eta-long normal forms to terms is injective.  NbE gives
an explicit left inverse, so no separate syntactic injectivity argument is
needed. -/
theorem Nf.toTm_injective : Function.Injective (@Nf.toTm Base Γ A) := by
  intro n m h
  have := congrArg normalizeNf h
  simpa only [normalizeNf_toTm] using this

/-- A term is canonical when it is the erasure of an eta-long normal form. -/
def IsCanonical (t : Tm Γ A) : Prop := ∃ n : Nf Γ A, n.toTm = t

/-- Canonical terms are exactly the fixed points of normalization. -/
theorem isCanonical_iff_normalizeTm_eq (t : Tm Γ A) :
    IsCanonical t ↔ normalizeTm t = t := by
  constructor
  · rintro ⟨n, rfl⟩
    exact normalizeTm_toTm n
  · intro h
    exact ⟨normalizeNf t, h⟩

/-- Every result produced by the normalizer is canonical. -/
theorem isCanonical_normalizeTm (t : Tm Γ A) : IsCanonical (normalizeTm t) :=
  (isCanonical_iff_normalizeTm_eq _).2 (normalizeTm_idem t)

/-- Renaming preserves canonical syntax. -/
theorem IsCanonical.rename {t : Tm Γ A} (h : IsCanonical t) (ρ : Ren Γ Δ) :
    IsCanonical (Tm.rename ρ t) := by
  rcases h with ⟨n, rfl⟩
  exact ⟨n.rename ρ, Nf.toTm_rename ρ n⟩

/-- Terms certified to be fixed points of normalization. -/
abbrev CanonicalTm (Γ : List (Ty Base)) (A : Ty Base) :=
  {t : Tm Γ A // normalizeTm t = t}

/-- Regard an eta-long normal form as a certified canonical term. -/
def Nf.toCanonicalTm (n : Nf Γ A) : CanonicalTm Γ A :=
  ⟨n.toTm, normalizeTm_toTm n⟩

/-- Recover the eta-long normal form represented by a certified canonical
term. -/
def CanonicalTm.toNf (t : CanonicalTm Γ A) : Nf Γ A := normalizeNf t.1

@[simp] theorem CanonicalTm.toNf_toCanonicalTm (n : Nf Γ A) :
    n.toCanonicalTm.toNf = n := normalizeNf_toTm n

@[simp] theorem Nf.toCanonicalTm_toNf (t : CanonicalTm Γ A) :
    t.toNf.toCanonicalTm = t := by
  apply Subtype.ext
  exact t.2

/-- A canonical term has a unique normal-form witness. -/
theorem isCanonical_existsUniqueNf {t : Tm Γ A} (h : IsCanonical t) :
    ∃ n : Nf Γ A, n.toTm = t ∧ ∀ m : Nf Γ A, m.toTm = t → m = n := by
  rcases h with ⟨n, rfl⟩
  refine ⟨n, rfl, ?_⟩
  intro m hm
  exact Nf.toTm_injective hm

end Cslib.Languages.LambdaCalculus.Stlc
