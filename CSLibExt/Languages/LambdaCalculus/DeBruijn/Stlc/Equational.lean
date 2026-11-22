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
# Semantic equational theory of STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Denotational

/-!
# Semantic equational theory of STLC

This file turns the denotational interpretation into an equational interface.
Semantic equality is an equivalence and a congruence, is preserved by renaming
and simultaneous substitution, validates beta and eta, and contains the
operational evaluation relation.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u v

variable {Base : Type u}
variable {I : Base → Type v}
variable {A B : Ty Base}
variable {Γ Δ : List (Ty Base)}

/-- Equality in a fixed set-theoretic model, at every semantic environment. -/
def SemEq (I : Base → Type v) (t u : Tm Γ A) : Prop :=
  ∀ η : Env I Γ, Tm.denote I t η = Tm.denote I u η

namespace SemEq

/-- Semantic equality is reflexive. -/
theorem refl (I : Base → Type v) (t : Tm Γ A) : SemEq I t t := fun _ ↦ rfl

/-- Semantic equality is symmetric. -/
theorem symm {t u : Tm Γ A} (h : SemEq I t u) : SemEq I u t := fun η ↦ (h η).symm

/-- Semantic equality is transitive. -/
theorem trans {t u w : Tm Γ A} (htu : SemEq I t u) (huw : SemEq I u w) :
    SemEq I t w := fun η ↦ (htu η).trans (huw η)

/-- Semantically equal functions and arguments have semantically equal applications. -/
theorem app {f g : Tm Γ (A ⇒ B)} {a b : Tm Γ A}
    (hfg : SemEq I f g) (hab : SemEq I a b) : SemEq I (.app f a) (.app g b) := by
  intro η
  simp only [Tm.denote_app]
  rw [hfg η, hab η]

/-- Lambda abstraction preserves semantic equality of bodies. -/
theorem lam {body body' : Tm (A :: Γ) B} (h : SemEq I body body') :
    SemEq I (.lam body) (.lam body') := by
  intro η
  simp only [Tm.denote_lam]
  funext a
  exact h (Env.cons a η)

/-- Renaming preserves semantic equality. -/
theorem rename {t u : Tm Γ A} (h : SemEq I t u) (ρ : Ren Γ Δ) :
    SemEq I (Tm.rename ρ t) (Tm.rename ρ u) := by
  intro η
  rw [Tm.denote_rename, Tm.denote_rename]
  exact h (Env.rename ρ η)

/-- Applying one substitution preserves semantic equality of terms. -/
theorem subst {t u : Tm Γ A} (h : SemEq I t u) (σ : Sub Γ Δ) :
    SemEq I (Tm.subst σ t) (Tm.subst σ u) := by
  intro η
  rw [Tm.denote_subst, Tm.denote_subst]
  exact h (Tm.denoteSub I σ η)

/-- Every one-step evaluation is a valid semantic equation. -/
theorem of_step {t u : Tm Γ A} (h : Step t u) : SemEq I t u := fun η ↦ h.denote_eq I η

/-- Every multi-step evaluation is a valid semantic equation. -/
theorem of_steps {t u : Tm Γ A} (h : Steps t u) : SemEq I t u := fun η ↦ h.denote_eq I η

/-- Beta is valid in every set-theoretic model. -/
theorem beta (I : Base → Type v) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    SemEq I (.app (.lam body) a) (Tm.instantiate body a) := by
  intro η
  exact (Tm.denote_instantiate I body a η).symm

/-- Eta is valid in every set-theoretic model. -/
theorem eta (I : Base → Type v) (f : Tm Γ (A ⇒ B)) :
    SemEq I (.lam (.app (Tm.weaken f) (.var .zero))) f := by
  intro η
  simp only [Tm.denote_lam, Tm.denote_app, Tm.denote_var]
  funext a
  rw [Tm.denote_weaken]
  rfl

end SemEq

/-- Pointwise semantic equality of simultaneous substitutions. -/
def SubSemEq (I : Base → Type v) (σ τ : Sub Γ Δ) : Prop :=
  ∀ {A} (x : Var Γ A) (η : Env I Δ), Tm.denote I (σ x) η = Tm.denote I (τ x) η

namespace SubSemEq

/-- Pointwise semantic equality is reflexive. -/
theorem refl (I : Base → Type v) (σ : Sub Γ Δ) : SubSemEq I σ σ := fun _ _ ↦ rfl

/-- Pointwise semantic equality is symmetric. -/
theorem symm {σ τ : Sub Γ Δ} (h : SubSemEq I σ τ) : SubSemEq I τ σ :=
  fun x η ↦ (h x η).symm

/-- Pointwise semantic equality is transitive. -/
theorem trans {σ τ υ : Sub Γ Δ} (hστ : SubSemEq I σ τ) (hτυ : SubSemEq I τ υ) :
    SubSemEq I σ υ := fun x η ↦ (hστ x η).trans (hτυ x η)

end SubSemEq

namespace SemEq

/-- Substituting pointwise semantically equal environments gives equal terms. -/
theorem subst_congr (t : Tm Γ A) {σ τ : Sub Γ Δ} (hστ : SubSemEq I σ τ) :
    SemEq I (Tm.subst σ t) (Tm.subst τ t) := by
  intro η
  rw [Tm.denote_subst, Tm.denote_subst]
  apply congrArg (Tm.denote I t)
  funext B x
  exact hστ x η

/-- Semantic equality is an equivalence relation in every model. -/
theorem equivalence (I : Base → Type v) : Equivalence (@SemEq Base A Γ I) :=
  ⟨refl I, symm, trans⟩

end SemEq

end Cslib.Languages.LambdaCalculus.Stlc
