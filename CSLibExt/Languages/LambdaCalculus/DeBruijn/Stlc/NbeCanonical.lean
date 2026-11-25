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

/-- **Reflection commutes with renaming.** For every type $A$, every renaming $\rho$ from a
context $\Gamma$ to a context $\Delta$, and every neutral term $n$ of type $A$ in context
$\Gamma$, transporting the semantic value obtained by reflecting $n$ at type $A$ along $\rho$
gives the reflection at type $A$ of the neutral term $n$ renamed by $\rho$. -/
theorem reflect_rename (A : Ty Base) (ρ : Ren Γ Δ) (n : Ne Γ A) :
    Sem.rename ρ A (reflect A n) = reflect A (n.rename ρ) := by
  induction A with
  | base => rfl
  | arr A B ihA ihB =>
    funext Θ σ a
    change reflect B (.app (n.rename (Var.comp ρ σ)) (quote A a)) =
      reflect B (.app ((n.rename ρ).rename σ) (quote A a))
    rw [Ne.rename_comp]

/-- **The identity environment under a binder.** Let $\Gamma$ be a context, $A$ a type, and
$\Gamma, A$ the context $\Gamma$ extended by a newest variable of type $A$. Transport the identity
semantic environment of $\Gamma$ (which reflects each variable as a neutral value) along the
weakening renaming from $\Gamma$ to $\Gamma, A$ that sends each variable to its successor, and
extend the result by the reflection at type $A$ of the newest variable of $\Gamma, A$. The
resulting semantic environment equals the identity semantic environment of $\Gamma, A$. -/
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

/-- **Evaluation respects pointwise equal environments.** Let $t$ be a term of type $A$ in
context $\Gamma$, and let $\xi$ and $\zeta$ be semantic environments interpreting the variables of
$\Gamma$ in a context $\Delta$. If $\xi(x) = \zeta(x)$ for every variable $x$ of $\Gamma$, of any
type, then evaluating $t$ in $\xi$ and evaluating $t$ in $\zeta$ give the same semantic value. -/
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

/-- **Evaluating a neutral term reflects it.** For every neutral term $n$ of type $A$ in context
$\Gamma$, evaluating the underlying term of $n$ in the identity semantic environment of $\Gamma$
gives the reflection of $n$ at type $A$. -/
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

/-- **Normal forms are fixed points of normalization.** For every beta-normal, eta-long normal
form $n$ of type $A$ in context $\Gamma$, normalizing the underlying term of $n$ by evaluation
returns the normal form $n$ itself. -/
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

/-- **Renormalizing a computed normal form.** For every term $t$ of type $A$ in context
$\Gamma$, normalizing the underlying term of the normal form that normalization by evaluation
computes from $t$ gives the same term as normalizing $t$. -/
@[simp] theorem normalizeTm_normalizeNf (t : Tm Γ A) :
    normalizeTm (normalizeNf t).toTm = normalizeTm t := by
  simp only [normalizeTm, normalizeNf_toTm]

/-- **Normalization by evaluation is idempotent.** For every term $t$ of type $A$ in context
$\Gamma$, normalizing the normalized term of $t$ by evaluation gives the normalized term of $t$
again. -/
@[simp] theorem normalizeTm_idem (t : Tm Γ A) :
    normalizeTm (normalizeTm t) = normalizeTm t := by
  exact normalizeTm_normalizeNf t

/-- **Normalization fixes the terms of normal forms.** For every eta-long normal form $n$ of
type $A$ in context $\Gamma$, normalizing the underlying term of $n$ returns that term
unchanged. -/
@[simp] theorem normalizeTm_toTm (n : Nf Γ A) : normalizeTm n.toTm = n.toTm := by
  simp only [normalizeTm, normalizeNf_toTm]

/-- **Erasing normal forms is injective.** For every context $\Gamma$ and type $A$, two
eta-long normal forms of type $A$ in context $\Gamma$ with the same underlying term are equal.

NbE gives an explicit left inverse, so no separate syntactic injectivity argument is
needed. -/
theorem Nf.toTm_injective : Function.Injective (@Nf.toTm Base Γ A) := by
  intro n m h
  have := congrArg normalizeNf h
  simpa only [normalizeNf_toTm] using this

/-- **Canonical terms.** A term $t$ of type $A$ in context $\Gamma$ is canonical when it is the
underlying term of some beta-normal, eta-long normal form of type $A$ in context $\Gamma$. -/
def IsCanonical (t : Tm Γ A) : Prop := ∃ n : Nf Γ A, n.toTm = t

/-- **Canonical terms are the fixed points of normalization.** A term $t$ of type $A$ in context
$\Gamma$ is canonical if and only if normalization by evaluation maps $t$ to itself, that is, the
term underlying the normal form computed for $t$ is $t$. -/
theorem isCanonical_iff_normalizeTm_eq (t : Tm Γ A) :
    IsCanonical t ↔ normalizeTm t = t := by
  constructor
  · rintro ⟨n, rfl⟩
    exact normalizeTm_toTm n
  · intro h
    exact ⟨normalizeNf t, h⟩

/-- **Normalized terms are canonical.** For every term $t$ of type $A$ in context $\Gamma$, the
term obtained by normalizing $t$ by evaluation is canonical. -/
theorem isCanonical_normalizeTm (t : Tm Γ A) : IsCanonical (normalizeTm t) :=
  (isCanonical_iff_normalizeTm_eq _).2 (normalizeTm_idem t)

/-- **Renaming preserves canonical terms.** If a term $t$ of type $A$ in context $\Gamma$ is
canonical, then for every renaming $\rho$ from $\Gamma$ to a context $\Delta$, the term
obtained by renaming $t$ along $\rho$ is canonical. -/
theorem IsCanonical.rename {t : Tm Γ A} (h : IsCanonical t) (ρ : Ren Γ Δ) :
    IsCanonical (Tm.rename ρ t) := by
  rcases h with ⟨n, rfl⟩
  exact ⟨n.rename ρ, Nf.toTm_rename ρ n⟩

/-- **Certified canonical terms.** For a context $\Gamma$ and a type $A$, a certified canonical
term of type $A$ in context $\Gamma$ is a term $t$ of type $A$ in context $\Gamma$ together with a
proof that $t$ is a fixed point of normalization by evaluation: the term underlying the normal
form computed for $t$ is $t$ itself. -/
abbrev CanonicalTm (Γ : List (Ty Base)) (A : Ty Base) :=
  {t : Tm Γ A // normalizeTm t = t}

/-- **Normal forms as canonical terms.** The canonical term of an eta-long normal form $n$ of
type $A$ in context $\Gamma$ is the underlying term of $n$, certified to be a fixed point of
normalization. -/
def Nf.toCanonicalTm (n : Nf Γ A) : CanonicalTm Γ A :=
  ⟨n.toTm, normalizeTm_toTm n⟩

/-- **The normal form of a canonical term.** For a canonical term $t$ of type $A$ in context
$\Gamma$, that is, a term that normalization returns unchanged, its normal form is the
eta-long normal form that normalization by evaluation computes from $t$. -/
def CanonicalTm.toNf (t : CanonicalTm Γ A) : Nf Γ A := normalizeNf t.1

@[simp] theorem CanonicalTm.toNf_toCanonicalTm (n : Nf Γ A) :
    n.toCanonicalTm.toNf = n := normalizeNf_toTm n

@[simp] theorem Nf.toCanonicalTm_toNf (t : CanonicalTm Γ A) :
    t.toNf.toCanonicalTm = t := by
  apply Subtype.ext
  exact t.2

/-- **Canonical terms have a unique normal form.** Let $t$ be a term of type $A$ in context
$\Gamma$. If $t$ is canonical, then there is exactly one beta-normal, eta-long normal form of type
$A$ in context $\Gamma$ whose underlying term is $t$. -/
theorem isCanonical_existsUniqueNf {t : Tm Γ A} (h : IsCanonical t) :
    ∃ n : Nf Γ A, n.toTm = t ∧ ∀ m : Nf Γ A, m.toTm = t → m = n := by
  rcases h with ⟨n, rfl⟩
  refine ⟨n, rfl, ?_⟩
  intro m hm
  exact Nf.toTm_injective hm

end Cslib.Languages.LambdaCalculus.Stlc
