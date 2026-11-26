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

/-- **Semantic equality of terms in a model.** Fix an interpretation $I$ of the base types as types.
Two terms $t$ and $u$ of the same type $A$ in the same context $\Gamma$ are semantically equal in
$I$ when, for every semantic environment $\eta$ for $\Gamma$, the denotation of $t$ in $I$ at $\eta$
equals the denotation of $u$ in $I$ at $\eta$. -/
def SemEq (I : Base → Type v) (t u : Tm Γ A) : Prop :=
  ∀ η : Env I Γ, Tm.denote I t η = Tm.denote I u η

namespace SemEq

/-- **Semantic equality is reflexive.** For every interpretation $I$ of the base types, every
term $t$ is semantically equal to itself in $I$: it has the same denotation as itself in every
environment. -/
theorem refl (I : Base → Type v) (t : Tm Γ A) : SemEq I t t := fun _ ↦ rfl

/-- **Symmetry of semantic equality of terms.** For every interpretation $I$ of the base types and
all terms $t$ and $u$ of the same type in the same context, if $t$ and $u$ are semantically equal
in $I$, then $u$ and $t$ are semantically equal in $I$. -/
theorem symm {t u : Tm Γ A} (h : SemEq I t u) : SemEq I u t := fun η ↦ (h η).symm

/-- **Transitivity of semantic equality of terms.** For every interpretation $I$ of the base types
and all terms $t$, $u$ and $w$ of the same type in the same context, if $t$ and $u$ are
semantically equal in $I$ and $u$ and $w$ are semantically equal in $I$, then $t$ and $w$ are
semantically equal in $I$. -/
theorem trans {t u w : Tm Γ A} (htu : SemEq I t u) (huw : SemEq I u w) :
    SemEq I t w := fun η ↦ (htu η).trans (huw η)

/-- **Semantic equality is a congruence for application.** Fix an interpretation $I$ of the base
types. If terms $f$ and $g$ of type $A \Rightarrow B$ in a context $\Gamma$ are semantically
equal in $I$ (they have the same denotation in every environment), and terms $a$ and $b$ of type
$A$ in $\Gamma$ are semantically equal in $I$, then the applications $f\,a$ and $g\,b$ are
semantically equal in $I$. -/
theorem app {f g : Tm Γ (A ⇒ B)} {a b : Tm Γ A}
    (hfg : SemEq I f g) (hab : SemEq I a b) : SemEq I (.app f a) (.app g b) := by
  intro η
  simp only [Tm.denote_app]
  rw [hfg η, hab η]

/-- **Semantic equality is a congruence for lambda abstraction.** Fix an interpretation $I$ of
the base types. If two terms of type $B$ in the context $\Gamma$ extended by a newest variable
of type $A$ are semantically equal in $I$ (they have the same denotation in every environment),
then their lambda abstractions, terms of type $A \Rightarrow B$ in $\Gamma$, are semantically
equal in $I$. -/
theorem lam {body body' : Tm (A :: Γ) B} (h : SemEq I body body') :
    SemEq I (.lam body) (.lam body') := by
  intro η
  simp only [Tm.denote_lam]
  funext a
  exact h (Env.cons a η)

/-- **Renaming preserves semantic equality.** Fix an interpretation $I$ of the base types. If
terms $t$ and $u$ of type $A$ in a context $\Gamma$ are semantically equal in $I$ (they have the
same denotation in every environment), then for every type-preserving renaming $\rho$ of the
variables of $\Gamma$ into a context $\Delta$, the renamed terms $\rho(t)$ and $\rho(u)$ are
semantically equal in $I$. -/
theorem rename {t u : Tm Γ A} (h : SemEq I t u) (ρ : Ren Γ Δ) :
    SemEq I (Tm.rename ρ t) (Tm.rename ρ u) := by
  intro η
  rw [Tm.denote_rename, Tm.denote_rename]
  exact h (Env.rename ρ η)

/-- **Substitution preserves semantic equality.** For every interpretation $I$ of the base types,
if two terms $t$ and $u$ of the same type $A$ in a context $\Gamma$ are semantically equal in $I$,
then for every simultaneous substitution $\sigma$ from $\Gamma$ to a context $\Delta$, the result
of applying $\sigma$ to $t$ and the result of applying $\sigma$ to $u$ are semantically equal in
$I$. -/
theorem subst {t u : Tm Γ A} (h : SemEq I t u) (σ : Sub Γ Δ) :
    SemEq I (Tm.subst σ t) (Tm.subst σ u) := by
  intro η
  rw [Tm.denote_subst, Tm.denote_subst]
  exact h (Tm.denoteSub I σ η)

/-- **Single-step evaluation is a semantic equation.** For every interpretation $I$ of the base
types, if a term $t$ reduces to a term $u$ in one call-by-value evaluation step, then $t$ and $u$
are semantically equal in $I$: they have the same denotation in every environment. -/
theorem of_step {t u : Tm Γ A} (h : Step t u) : SemEq I t u := fun η ↦ h.denote_eq I η

/-- **Multi-step evaluation is a semantic equation.** For every interpretation $I$ of the base
types, if a term $t$ reduces to a term $u$ in zero or more call-by-value evaluation steps, then
$t$ and $u$ are semantically equal in $I$: they have the same denotation in every environment. -/
theorem of_steps {t u : Tm Γ A} (h : Steps t u) : SemEq I t u := fun η ↦ h.denote_eq I η

/-- **Beta is sound for the denotational semantics.** For every interpretation $I$ of the base
types, every term $t$ of type $B$ in the context $\Gamma$ extended by a newest variable of type
$A$, and every term $a$ of type $A$ in $\Gamma$, the redex $(\lambda.\,t)\,a$ is semantically
equal in $I$ (has the same denotation in every environment) to the instantiation $t[a]$, which
replaces the newest free variable of $t$ by $a$.

The argument $a$ need not be a value. -/
theorem beta (I : Base → Type v) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    SemEq I (.app (.lam body) a) (Tm.instantiate body a) := by
  intro η
  exact (Tm.denote_instantiate I body a η).symm

/-- **Eta is sound for the denotational semantics.** For every interpretation $I$ of the base
types and every term $f$ of type $A \Rightarrow B$ in a context $\Gamma$, let $f'$ be the
weakening of $f$ to the context $\Gamma$ extended by a newest variable $x$ of type $A$. Then the
term $\lambda x.\, f'\,x$, which binds $x$, is semantically equal to $f$ in $I$ (has the same
denotation in every environment). -/
theorem eta (I : Base → Type v) (f : Tm Γ (A ⇒ B)) :
    SemEq I (.lam (.app (Tm.weaken f) (.var .zero))) f := by
  intro η
  simp only [Tm.denote_lam, Tm.denote_app, Tm.denote_var]
  funext a
  rw [Tm.denote_weaken]
  rfl

end SemEq

/-- **Pointwise semantic equality of substitutions.** Fix an interpretation $I$ of the base types
as types. Two simultaneous substitutions $\sigma$ and $\tau$ from a context $\Gamma$ to a context
$\Delta$ are pointwise semantically equal in $I$ when, for every variable $x$ of $\Gamma$ (of any
type) and every semantic environment $\eta$ for $\Delta$, the denotation of the term $\sigma(x)$ in
$I$ at $\eta$ equals the denotation of the term $\tau(x)$ in $I$ at $\eta$. -/
def SubSemEq (I : Base → Type v) (σ τ : Sub Γ Δ) : Prop :=
  ∀ {A} (x : Var Γ A) (η : Env I Δ), Tm.denote I (σ x) η = Tm.denote I (τ x) η

namespace SubSemEq

/-- **Pointwise semantic equality of substitutions is reflexive.** For every interpretation $I$
of the base types and every simultaneous substitution $\sigma$ that replaces each variable of a
context $\Gamma$ by a term of the same type in a context $\Delta$, $\sigma$ is pointwise
semantically equal to itself in $I$: for every variable $x$ of $\Gamma$, the term $\sigma(x)$
has the same denotation as itself in every environment for $\Delta$. -/
theorem refl (I : Base → Type v) (σ : Sub Γ Δ) : SubSemEq I σ σ := fun _ _ ↦ rfl

/-- **Symmetry of pointwise semantic equality of substitutions.** For every interpretation $I$ of
the base types and all simultaneous substitutions $\sigma$ and $\tau$ from a context $\Gamma$ to a
context $\Delta$, if $\sigma$ and $\tau$ are pointwise semantically equal in $I$, then $\tau$ and
$\sigma$ are pointwise semantically equal in $I$. -/
theorem symm {σ τ : Sub Γ Δ} (h : SubSemEq I σ τ) : SubSemEq I τ σ :=
  fun x η ↦ (h x η).symm

/-- **Transitivity of pointwise semantic equality of substitutions.** For every interpretation $I$
of the base types and all simultaneous substitutions $\sigma$, $\tau$ and $\upsilon$ from a context
$\Gamma$ to a context $\Delta$, if $\sigma$ and $\tau$ are pointwise semantically equal in $I$ and
$\tau$ and $\upsilon$ are pointwise semantically equal in $I$, then $\sigma$ and $\upsilon$ are
pointwise semantically equal in $I$. -/
theorem trans {σ τ υ : Sub Γ Δ} (hστ : SubSemEq I σ τ) (hτυ : SubSemEq I τ υ) :
    SubSemEq I σ υ := fun x η ↦ (hστ x η).trans (hτυ x η)

end SubSemEq

namespace SemEq

/-- **Semantically equal substitutions give semantically equal results.** For every interpretation
$I$ of the base types, every term $t$ of type $A$ in a context $\Gamma$, and all simultaneous
substitutions $\sigma$ and $\tau$ from $\Gamma$ to a context $\Delta$ that are pointwise
semantically equal in $I$, the result of applying $\sigma$ to $t$ and the result of applying $\tau$
to $t$ are semantically equal in $I$. -/
theorem subst_congr (t : Tm Γ A) {σ τ : Sub Γ Δ} (hστ : SubSemEq I σ τ) :
    SemEq I (Tm.subst σ t) (Tm.subst τ t) := by
  intro η
  rw [Tm.denote_subst, Tm.denote_subst]
  apply congrArg (Tm.denote I t)
  funext B x
  exact hστ x η

/-- **Semantic equality is an equivalence relation.** For every interpretation $I$ of the base
types, every context $\Gamma$ and every type $A$, semantic equality in $I$ of terms of type $A$
in $\Gamma$ (having the same denotation in every environment) is reflexive, symmetric and
transitive. -/
theorem equivalence (I : Base → Type v) : Equivalence (@SemEq Base A Γ I) :=
  ⟨refl I, symm, trans⟩

end SemEq

end Cslib.Languages.LambdaCalculus.Stlc
