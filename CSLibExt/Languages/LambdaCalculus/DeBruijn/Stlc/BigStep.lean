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

/-- **Big-step call-by-value evaluation in the simply typed lambda calculus.** Fix a typing
context $\Gamma$. For terms $t$ and $v$ of the same type in context $\Gamma$, the big-step
evaluation relation $t \Downarrow v$ is the least relation such that every lambda abstraction
$\lambda.\,b$ evaluates to itself, and an application $f\,a$ evaluates to $v$ whenever
$f \Downarrow \lambda.\,b$, $a \Downarrow u$ and $b[u] \Downarrow v$, where $b[u]$ is the body $b$
with its newest free variable replaced by $u$.

The application rule fixes a left-to-right order: first the function, then the argument, then
the instantiated body. -/
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

/-- **Big-step evaluation produces values.** In the call-by-value simply typed lambda calculus,
if a term $t$ of type $A$ in context $\Gamma$ evaluates by big-step evaluation to a term $v$,
written $t \Downarrow v$, then $v$ is a value, that is, a lambda abstraction. -/
theorem value {t v : Tm Γ A} (h : t ⇓ v) : Value v := by
  induction h with
  | lam => exact .lam _
  | app _ _ _ _ _ hbody => exact hbody

/-- **Values evaluate to themselves.** Every value $v$, that is, every lambda abstraction, of any
type in any typing context evaluates to itself in the big-step semantics: $v \Downarrow v$. -/
theorem value_self {v : Tm Γ A} (hv : Value v) : v ⇓ v := by
  cases hv with
  | lam body => exact .lam body

/-- **Big-step evaluation implies small-step evaluation.** Let $t$ and $v$ be terms of the same
type in the same typing context. If $t$ evaluates to $v$ in the big-step semantics, written
$t \Downarrow v$, then $t$ reduces to $v$ in finitely many (possibly zero) left-to-right
call-by-value steps. -/
theorem to_steps {t v : Tm Γ A} (h : t ⇓ v) : Steps t v := by
  induction h with
  | lam => exact .refl
  | @app A B f a body va v hf ha hbody ihf iha ihbody =>
      exact (Steps.appFun a ihf).trans <|
        (Steps.appArg (.lam body) iha).trans <|
          (Relation.ReflTransGen.single (.beta ha.value)).trans ihbody

/-- **Big-step evaluation is closed under backward reduction steps.** Let $t$, $t'$ and $v$ be
terms of the same type $A$ in the same typing context $\Gamma$. If $t$ reduces to $t'$ in one
left-to-right call-by-value step and $t'$ evaluates to $v$ in the big-step semantics, written
$t' \Downarrow v$, then $t \Downarrow v$. -/
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

/-- **Big-step evaluation is closed under backward multi-step reduction.** Let $t$, $t'$ and $v$
be terms of the same type $A$ in the same typing context $\Gamma$. If $t$ reduces to $t'$ in
finitely many (possibly zero) left-to-right call-by-value steps and $t'$ evaluates to $v$ in the
big-step semantics, written $t' \Downarrow v$, then $t \Downarrow v$. -/
theorem anti_steps {t t' v : Tm Γ A} (hsteps : Steps t t') (heval : t' ⇓ v) : t ⇓ v := by
  induction hsteps with
  | refl => exact heval
  | tail _ hstep ih => exact ih (anti_step hstep heval)

/-- **Small-step evaluation to a value implies big-step evaluation.** Let $t$ and $v$ be terms of
the same type in the same typing context. If $t$ reduces to $v$ in finitely many (possibly zero)
left-to-right call-by-value steps and $v$ is a value, then $t$ evaluates to $v$ in the big-step
semantics, written $t \Downarrow v$. -/
theorem of_steps {t v : Tm Γ A} (hsteps : Steps t v) (hv : Value v) : t ⇓ v :=
  anti_steps hsteps (value_self hv)

/-- **Big-step evaluation is small-step evaluation to a value.** For terms $t$ and $v$ of the
same type in the same typing context, $t$ evaluates to $v$ in the big-step semantics, written
$t \Downarrow v$, if and only if $t$ reduces to $v$ in finitely many (possibly zero)
left-to-right call-by-value steps and $v$ is a value, that is, a lambda abstraction. -/
theorem iff_steps_value {t v : Tm Γ A} : t ⇓ v ↔ Steps t v ∧ Value v := by
  constructor
  · intro h
    exact ⟨h.to_steps, h.value⟩
  · rintro ⟨hsteps, hv⟩
    exact of_steps hsteps hv

/-- **Determinism of big-step evaluation in the simply typed lambda calculus.** For every typing
context $\Gamma$ and type $A$, if a term $t$ of type $A$ in context $\Gamma$ evaluates in the
big-step call-by-value semantics both to $v$ and to $w$, written $t \Downarrow v$ and
$t \Downarrow w$, then $v = w$. -/
theorem deterministic {t v w : Tm Γ A} (htv : t ⇓ v) (htw : t ⇓ w) : v = w := by
  exact Steps.value_unique htv.to_steps htv.value htw.to_steps htw.value

/-- **Closed simply typed terms have a big-step evaluation.** For every type $A$ and every closed
term $t$ of type $A$, that is, a term in the empty typing context, there is a term $v$ such that
$t$ evaluates to $v$ in the big-step call-by-value semantics, written $t \Downarrow v$. -/
theorem exists_closed (t : Tm [] A) : ∃ v, t ⇓ v := by
  rcases terminates_closed t with ⟨v, htv, hv⟩
  exact ⟨v, of_steps htv hv⟩

end Eval

/-- **Termination in terms of big-step evaluation.** For every closed term $t$ of type $A$, that
is, a term in the empty typing context, $t$ terminates (it reduces to a value in finitely many
left-to-right call-by-value steps) if and only if there is a term $v$ such that $t$ evaluates to
$v$ in the big-step semantics, written $t \Downarrow v$. -/
theorem terminates_iff_eval {t : Tm [] A} : Terminates t ↔ ∃ v, t ⇓ v := by
  constructor
  · rintro ⟨v, htv, hv⟩
    exact ⟨v, Eval.of_steps htv hv⟩
  · rintro ⟨v, htv⟩
    exact ⟨v, htv.to_steps, htv.value⟩

end Cslib.Languages.LambdaCalculus.Stlc
