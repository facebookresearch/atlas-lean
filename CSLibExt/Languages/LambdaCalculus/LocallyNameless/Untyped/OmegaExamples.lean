/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Relation.Defs
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction

/-!
# `Ω` has no normal form, and `K I Ω` normalizes by leftmost reduction

Two classical examples for CSLib's locally nameless untyped λ-terms
(`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term`), full β-reduction `FullBeta` (written `⭢βᶠ`,
with reflexive-transitive closure `↠βᶠ`) and leftmost reduction `Leftmost` (`⭢ℓ`, `↠ℓ`):

* `Omega`, the term `Ω = (λx. x x) (λx. x x)`, reduces to itself (`Omega_step_self`) and to nothing
  else (`eq_Omega_of_step`, `eq_Omega_of_steps`), so it has no normal form
  (`not_normalizable_Omega`);
* `K I Ω`, with `K = λx. λy. x` and `I = λx. x`, reaches `I` by leftmost reduction
  (`KIOmega_leftmost_I`), and `I` is a normal form (`normal_I`). Reducing inside `Ω` instead loops,
  so the reduction strategy matters.

Normal forms are relational: `Relation.Normal FullBeta`. The four terms are closed and locally
closed (`omega_lc`, `Omega_lc`, `K_lc`, `I_lc`, `KIOmega_lc`). Names come from a type with fresh
elements (`HasFresh Var`): over a one-element name type the cofinite ξ-rule of `FullBeta` holds
vacuously, every abstraction reduces, and the irreducibility statements fail.

## References

* H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland, 1984.
-/

@[expose] public section

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.OmegaExamples

open Term
open scoped Term

universe u

/-- `ω = λx. x x`, written `λ. 0 0` with de Bruijn indices. -/
def omega {Var : Type u} : Term Var := .abs (.app (.bvar 0) (.bvar 0))

/-- `Ω = ω ω = (λx. x x) (λx. x x)`. -/
def Omega {Var : Type u} : Term Var := .app omega omega

/-- The combinator `K = λx. λy. x`, written `λ. λ. 1`. -/
def K {Var : Type u} : Term Var := .abs (.abs (.bvar 1))

/-- The combinator `I = λx. x`, written `λ. 0`. -/
def I {Var : Type u} : Term Var := .abs (.bvar 0)

/-! ### Local closure -/

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `ω` is
locally closed. -/
theorem omega_lc {Var : Type u} [HasFresh Var] : (omega : Term Var).LC := by
  exact (lcAt_iff_LC _).mp rfl

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `Ω` is
locally closed. -/
theorem Omega_lc {Var : Type u} [HasFresh Var] : (Omega : Term Var).LC := by
  exact .app omega_lc omega_lc

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `K` is
locally closed. -/
theorem K_lc {Var : Type u} [HasFresh Var] : (K : Term Var).LC := by
  exact (lcAt_iff_LC _).mp rfl

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `I` is
locally closed. -/
theorem I_lc {Var : Type u} [HasFresh Var] : (I : Term Var).LC := by
  exact (lcAt_iff_LC _).mp rfl

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `K I Ω`
is locally closed. -/
theorem KIOmega_lc {Var : Type u} [HasFresh Var] : (app (app K I) Omega : Term Var).LC := by
  exact .app (.app K_lc I_lc) Omega_lc

/-! ### `Ω` has no normal form -/

/-- A free variable does not reduce. -/
private theorem not_fullBeta_fvar {Var : Type u} (x : Var) (N : Term Var) : ¬ fvar x ⭢βᶠ N := by
  intro h
  cases h with
  | base h => cases h

/-- An application of a free variable to a free variable does not reduce. -/
private theorem not_fullBeta_app_fvar_fvar {Var : Type u} (x y : Var) (N : Term Var) :
    ¬ app (fvar x) (fvar y) ⭢βᶠ N := by
  intro h
  rcases FullBeta.invert_step_app_fvar h with ⟨M, -, hM⟩ | ⟨_, hM, -⟩
  · exact not_fullBeta_fvar x M hM
  · cases hM

/-- `ω` does not reduce: under its binder it is `x x` for a fresh name `x`. -/
private theorem not_fullBeta_omega {Var : Type u} [HasFresh Var] (N : Term Var) :
    ¬ omega ⭢βᶠ N := by
  intro h
  cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨x, hx⟩ := fresh_exists xs
    exact not_fullBeta_app_fvar_fvar x x _ (h x hx)

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `Ω`
contracts to itself: `(λx. x x) ω ⭢βᶠ ω ω`. -/
theorem Omega_step_self {Var : Type u} [HasFresh Var] : (Omega : Term Var) ⭢βᶠ Omega := by
  exact .base (.beta omega_lc omega_lc)

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), every
one-step full β-reduct of `Ω` is `Ω`. -/
theorem eq_Omega_of_step {Var : Type u} [HasFresh Var] :
    ∀ N : Term Var, Omega ⭢βᶠ N → N = Omega := by
  intro N h
  cases h with
  | base h =>
    cases h
    rfl
  | appL _ h => exact absurd h (not_fullBeta_omega _)
  | appR _ h => exact absurd h (not_fullBeta_omega _)

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), every
term that `Ω` reaches by full β-reduction is `Ω`. -/
theorem eq_Omega_of_steps {Var : Type u} [HasFresh Var] :
    ∀ N : Term Var, Omega ↠βᶠ N → N = Omega := by
  intro N h
  induction h with
  | refl => rfl
  | tail _ h ih =>
    subst ih
    exact eq_Omega_of_step _ h

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `Ω` has
no normal form. -/
theorem not_normalizable_Omega {Var : Type u} [HasFresh Var] :
    ¬ Relation.Normalizable FullBeta (Omega : Term Var) := by
  rintro ⟨N, hsteps, hnormal⟩
  obtain rfl := eq_Omega_of_steps N hsteps
  exact hnormal ⟨Omega, Omega_step_self⟩

/-! ### `K I Ω` normalizes by leftmost reduction -/

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`),
leftmost reduction takes `K I Ω` to `I`, through `(λy. I) Ω`. -/
theorem KIOmega_leftmost_I {Var : Type u} [HasFresh Var] :
    (app (app K I) Omega : Term Var) ↠ℓ I := by
  have h₁ : (app (app K I) Omega : Term Var) ⭢ℓ app (abs I) Omega :=
    BetaAt.appNoAbsL (BetaAt.outer K_lc I_lc) nofun
  have h₂ : (app (abs I) Omega : Term Var) ⭢ℓ I :=
    BetaAt.outer ((lcAt_iff_LC _).mp rfl) Omega_lc
  exact .tail (.single h₁) h₂

/-- When a fresh name can be chosen outside every finite set of names (`HasFresh Var`), `I` is
a normal form. -/
theorem normal_I {Var : Type u} [HasFresh Var] : Relation.Normal FullBeta (I : Term Var) := by
  rintro ⟨N, h⟩
  cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨x, hx⟩ := fresh_exists xs
    exact not_fullBeta_fvar x _ (h x hx)

end Cslib.LambdaCalculus.LocallyNameless.Untyped.OmegaExamples
