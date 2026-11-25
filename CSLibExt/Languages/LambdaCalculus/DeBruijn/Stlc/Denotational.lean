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
# Denotational semantics for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.BigStep

/-!
# Denotational semantics for STLC

Simple types are interpreted as Lean types and arrows as function spaces.
Terms are interpreted in type-indexed environments.  The main substitution
lemma shows that syntactic simultaneous substitution agrees with semantic
environment composition; beta reduction and all operational evaluation then
preserve denotation.

The construction follows the set-theoretic presentation in the
[PLFA Denotational chapter](https://plfa.github.io/Denotational/), specialized
to the intrinsically typed de Bruijn calculus developed in this directory.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u v

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ Δ : List (Ty Base)}
variable {I : Base → Type v}

namespace Ty

/-- **Denotation of simple types.** Given an interpretation $I$ assigning a type $I(b)$ to each
base type $b$, the denotation $[\![A]\!]_I$ of a simple type $A$ is defined by recursion on $A$:
a base type $b$ denotes $I(b)$, and a function type $A \Rightarrow B$ denotes the type of all
functions from $[\![A]\!]_I$ to $[\![B]\!]_I$. -/
def denote (I : Base → Type v) : Ty Base → Type v
  | .base b => I b
  | .arr A B => denote I A → denote I B

@[simp] theorem denote_base (I : Base → Type v) (b : Base) : denote I (.base b) = I b := rfl

@[simp] theorem denote_arr (I : Base → Type v) (A B : Ty Base) :
    denote I (A ⇒ B) = (denote I A → denote I B) := rfl

end Ty

/-- **Semantic environments for the denotational semantics of STLC.** Given an interpretation $I$
assigning a type to each base type and a typing context $\Gamma$ (a list of simple types), an
environment for $\Gamma$ assigns to every variable $x$ of $\Gamma$, of any simple type $A$, an
element of the denotation $[\![A]\!]_I$. -/
abbrev Env (I : Base → Type v) (Γ : List (Ty Base)) :=
  ∀ {A}, Var Γ A → Ty.denote I A

namespace Env

/-- **Extending a semantic environment in STLC.** Given an interpretation $I$ of the base types, a
value $a$ in the denotation of a type $A$ and an environment $\eta$ for a context $\Gamma$, the
extended environment for the context $A :: \Gamma$ sends the newest variable to $a$ and the
successor $\mathrm{succ}\,x$ of each variable $x$ of $\Gamma$ to $\eta(x)$. -/
def cons (a : Ty.denote I A) (η : Env I Γ) : Env I (A :: Γ)
  | _, .zero => a
  | _, .succ x => η x

@[simp] theorem cons_zero (a : Ty.denote I A) (η : Env I Γ) : cons a η .zero = a := rfl

@[simp] theorem cons_succ (a : Ty.denote I A) (η : Env I Γ) (x : Var Γ B) :
    cons a η (.succ x) = η x := rfl

/-- **Renaming an environment.** Given a renaming $\rho$ from context $\Gamma$ to context
$\Delta$ (a type-preserving map from the variables of $\Gamma$ to those of $\Delta$) and an
environment $\eta$ for $\Delta$, the renamed environment for $\Gamma$ sends each variable $x$ of
$\Gamma$ to $\eta(\rho(x))$; that is, it is the composite $\eta \circ \rho$. -/
def rename (ρ : Ren Γ Δ) (η : Env I Δ) : Env I Γ := fun x ↦ η (ρ x)

end Env

namespace Tm

/-- **Denotation of an STLC term.** Given an interpretation $I$ of the base types, the denotation of
a well-typed term $t$ of type $A$ in context $\Gamma$ in an environment $\eta$ for $\Gamma$ is the
element of the denotation of $A$ defined by recursion on $t$: a variable $x$ denotes $\eta(x)$, an
application $f\,a$ denotes the denotation of $f$ applied to the denotation of $a$ (both in
$\eta$), and an abstraction $\lambda.\,b$ denotes the function sending each value $a$ of
its argument type to the denotation of the body $b$ in $\eta$ extended by $a$ for the newest
variable. -/
def denote (I : Base → Type v) : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Env I Γ → Ty.denote I A
  | _, _, .var x, η => η x
  | _, _, .app f a, η => denote I f η (denote I a η)
  | _, _, .lam body, η => fun a ↦ denote I body (Env.cons a η)

@[simp] theorem denote_var (I : Base → Type v) (x : Var Γ A) (η : Env I Γ) :
    denote I (.var x) η = η x := rfl

@[simp] theorem denote_app (I : Base → Type v) (f : Tm Γ (A ⇒ B)) (a : Tm Γ A)
    (η : Env I Γ) : denote I (.app f a) η = denote I f η (denote I a η) := rfl

@[simp] theorem denote_lam (I : Base → Type v) (body : Tm (A :: Γ) B) (η : Env I Γ) :
    denote I (.lam body) η = fun a ↦ denote I body (Env.cons a η) := rfl

/-- **Renaming lemma for STLC denotation.** For every interpretation $I$ of the base types, every
type-preserving renaming $\rho$ from context $\Gamma$ to context $\Delta$, every term $t$ in
context $\Gamma$ and every environment $\eta$ for $\Delta$, the denotation in $\eta$ of the term
obtained by renaming the variables of $t$ along $\rho$ equals the denotation of $t$ in the
environment that sends each variable $x$ of $\Gamma$ to $\eta(\rho(x))$. -/
theorem denote_rename (I : Base → Type v) (ρ : Ren Γ Δ) (t : Tm Γ A) (η : Env I Δ) :
    denote I (rename ρ t) η = denote I t (Env.rename ρ η) := by
  induction t generalizing Δ with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [rename_lam, denote_lam]
      funext a
      rw [ih]
      apply congrArg (denote I body)
      funext C x
      cases x <;> rfl

/-- **Weakening preserves STLC denotation.** For every interpretation $I$ of the base types, every
term $t$ of type $A$ in context $\Gamma$, every type $B$, every value $a$ in the denotation of $B$
and every environment $\eta$ for $\Gamma$, the weakening of $t$ to the context $B :: \Gamma$ has,
in the environment that extends $\eta$ by $a$ for the newest variable, the same denotation as $t$
in $\eta$. -/
theorem denote_weaken (I : Base → Type v) (t : Tm Γ A) (a : Ty.denote I B) (η : Env I Γ) :
    denote I (weaken (B := B) t) (Env.cons a η) = denote I t η := by
  rw [weaken, denote_rename]
  apply congrArg (denote I t)
  funext C x
  rfl

/-- **Denotation of an STLC substitution.** Given an interpretation $I$ of the base types, a
type-preserving substitution $\sigma$ mapping each variable of a context $\Gamma$ to a term in a
context $\Delta$, and an environment $\eta$ for $\Delta$, this is the environment for $\Gamma$
that sends each variable $x$ to the denotation of $\sigma(x)$ in $\eta$. -/
def denoteSub (I : Base → Type v) (σ : Sub Γ Δ) (η : Env I Δ) : Env I Γ :=
  fun x ↦ denote I (σ x) η

/-- **Substitution lemma for STLC denotation.** For every interpretation $I$ of the base types,
every type-preserving substitution $\sigma$ mapping each variable of a context $\Gamma$ to a term
in a context $\Delta$, every term $t$ in context $\Gamma$ and every environment $\eta$ for
$\Delta$, the denotation in $\eta$ of $t$ with $\sigma$ applied simultaneously to its variables
equals the denotation of $t$ in the environment that sends each variable $x$ of $\Gamma$ to the
denotation of $\sigma(x)$ in $\eta$. -/
theorem denote_subst (I : Base → Type v) (σ : Sub Γ Δ) (t : Tm Γ A) (η : Env I Δ) :
    denote I (subst σ t) η = denote I t (denoteSub I σ η) := by
  induction t generalizing Δ with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam, denote_lam]
      funext a
      rw [ih]
      apply congrArg (denote I body)
      funext C x
      cases x with
      | zero => rfl
      | succ x => exact denote_weaken I (σ x) a η

/-- **Denotation of an instantiated STLC body.** For every interpretation $I$ of the base types,
every term $b$ of type $B$ in context $A :: \Gamma$, every term $a$ of type $A$ in context $\Gamma$
and every environment $\eta$ for $\Gamma$, the denotation in $\eta$ of $b$ with its newest variable
replaced by $a$ equals the denotation of $b$ in the environment that extends $\eta$ by the
denotation of $a$ in $\eta$ for the newest variable. -/
theorem denote_instantiate (I : Base → Type v) (body : Tm (A :: Γ) B) (a : Tm Γ A)
    (η : Env I Γ) :
    denote I (instantiate body a) η = denote I body (Env.cons (denote I a η) η) := by
  rw [instantiate, denote_subst]
  apply congrArg (denote I body)
  funext C x
  cases x <;> rfl

end Tm

namespace Step

/-- **One reduction step preserves STLC denotation.** For every interpretation $I$ of the base
types, if a term $t$ reduces to $t'$ in one step of call-by-value reduction, then $t$ and $t'$
have the same denotation in every environment $\eta$ for their context. -/
theorem denote_eq (I : Base → Type v) {t t' : Tm Γ A} (h : Step t t') (η : Env I Γ) :
    Tm.denote I t η = Tm.denote I t' η := by
  induction h with
  | appFun hstep ih =>
      simp only [Tm.denote_app]
      rw [ih η]
  | appArg _ hstep ih =>
      simp only [Tm.denote_app]
      rw [ih η]
  | beta _ => exact (Tm.denote_instantiate I _ _ η).symm

end Step

namespace Steps

/-- **Multi-step reduction preserves STLC denotation.** For every interpretation $I$ of the base
types, if a term $t$ reduces to $t'$ in zero or more steps of call-by-value reduction, then $t$
and $t'$ have the same denotation in every environment $\eta$ for their context. -/
theorem denote_eq (I : Base → Type v) {t t' : Tm Γ A} (h : Steps t t') (η : Env I Γ) :
    Tm.denote I t η = Tm.denote I t' η := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.denote_eq I η)

end Steps

namespace Eval

/-- **Big-step evaluation preserves STLC denotation.** For every interpretation $I$ of the base
types, if a term $t$ evaluates to $v$ under call-by-value big-step evaluation, then $t$ and $v$
have the same denotation in every environment $\eta$ for their context. -/
theorem denote_eq (I : Base → Type v) {t value : Tm Γ A} (h : Eval t value)
    (η : Env I Γ) : Tm.denote I t η = Tm.denote I value η :=
  h.to_steps.denote_eq I η

end Eval

end Cslib.Languages.LambdaCalculus.Stlc
