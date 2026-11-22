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
# Big-step semantics for call-by-value STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Normalization

/-!
# Big-step semantics for call-by-value STLC

This file gives a natural semantics for the intrinsically typed calculus and
proves it equivalent to small-step evaluation to a value.  The application
rule makes the evaluation order explicit: evaluate the function to a lambda,
then the argument to a value, and finally evaluate the instantiated body.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ : List (Ty Base)}

/-- Left-to-right call-by-value big-step evaluation. -/
inductive Eval : {A : Ty Base} → Tm Γ A → Tm Γ A → Prop where
  | lam {A B : Ty Base} (body : Tm (A :: Γ) B) : Eval (.lam body) (.lam body)
  | app {A B : Ty Base} {f : Tm Γ (A ⇒ B)} {a : Tm Γ A}
      {body : Tm (A :: Γ) B} {va : Tm Γ A} {v : Tm Γ B} :
      Eval f (.lam body) →
      Eval a va →
      Eval (Tm.instantiate body va) v →
      Eval (.app f a) v

infix:50 " ⇓ " => Eval

namespace Eval

/-- The result of a big-step evaluation is a value. -/
theorem value {t v : Tm Γ A} (h : t ⇓ v) : Value v := by
  induction h with
  | lam => exact .lam _
  | app _ _ _ _ _ hbody => exact hbody

/-- Every value evaluates to itself. -/
theorem value_self {v : Tm Γ A} (hv : Value v) : v ⇓ v := by
  cases hv with
  | lam body => exact .lam body

/-- Big-step evaluation is sound with respect to multi-step evaluation. -/
theorem to_steps {t v : Tm Γ A} (h : t ⇓ v) : Steps t v := by
  induction h with
  | lam => exact .refl
  | @app A B f a body va v hf ha hbody ihf iha ihbody =>
      exact (Steps.appFun a ihf).trans <|
        (Steps.appArg (.lam body) iha).trans <|
          (Relation.ReflTransGen.single (.beta ha.value)).trans ihbody

/-- One inverse small step can be prepended to a big-step evaluation. -/
theorem anti_step {t t' v : Tm Γ A} (hstep : Step t t') (heval : t' ⇓ v) : t ⇓ v := by
  induction hstep with
  | @appFun A B Γ f f' a hff' ih =>
      cases heval with
      | @app _ _ _ _ body va v hf' ha hbody =>
          exact .app (ih hf') ha hbody
  | @appArg A B Γ f a a' hvf haa' ih =>
      cases hvf with
      | lam body =>
          cases heval with
          | @app _ _ _ _ body' va v hf ha' hbody =>
              cases hf
              exact .app (.lam body) (ih ha') hbody
  | @beta A B Γ body a hva =>
      exact .app (.lam body) (value_self hva) heval

/-- A finite inverse small-step prefix can be prepended to a big-step evaluation. -/
theorem anti_steps {t t' v : Tm Γ A} (hsteps : Steps t t') (heval : t' ⇓ v) : t ⇓ v := by
  induction hsteps with
  | refl => exact heval
  | tail _ hstep ih => exact ih (anti_step hstep heval)

/-- Small-step evaluation to a value is complete for the big-step semantics. -/
theorem of_steps {t v : Tm Γ A} (hsteps : Steps t v) (hv : Value v) : t ⇓ v :=
  anti_steps hsteps (value_self hv)

/-- Big-step and small-step evaluation agree exactly on value results. -/
theorem iff_steps_value {t v : Tm Γ A} : t ⇓ v ↔ Steps t v ∧ Value v := by
  constructor
  · intro h
    exact ⟨h.to_steps, h.value⟩
  · rintro ⟨hsteps, hv⟩
    exact of_steps hsteps hv

/-- Big-step evaluation is deterministic in every typing context. -/
theorem deterministic {t v w : Tm Γ A} (htv : t ⇓ v) (htw : t ⇓ w) : v = w := by
  exact Steps.value_unique htv.to_steps htv.value htw.to_steps htw.value

/-- Every closed well-typed term has a big-step evaluation. -/
theorem exists_closed (t : Tm [] A) : ∃ v, t ⇓ v := by
  rcases terminates_closed t with ⟨v, htv, hv⟩
  exact ⟨v, of_steps htv hv⟩

end Eval

/-- Termination can equivalently be stated using big-step evaluation. -/
theorem terminates_iff_eval {t : Tm [] A} : Terminates t ↔ ∃ v, t ⇓ v := by
  constructor
  · rintro ⟨v, htv, hv⟩
    exact ⟨v, Eval.of_steps htv hv⟩
  · rintro ⟨v, htv⟩
    exact ⟨v, htv.to_steps, htv.value⟩

end Cslib.Languages.LambdaCalculus.Stlc
