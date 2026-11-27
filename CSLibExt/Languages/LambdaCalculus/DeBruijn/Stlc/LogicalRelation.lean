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
# A logical relation for call-by-value STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Semantics
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.SubstitutionLaws

/-!
# A logical relation for call-by-value STLC

This file proves termination of closed terms in the intrinsically typed simply
typed lambda calculus.  The proof is the standard Tait logical-relations
argument, adapted to the left-to-right call-by-value semantics in
`Semantics.lean`.

The organization follows the reducibility proof in the
[Software Foundations normalization chapter][sf-norm]: first establish that
reducibility is invariant under evaluation, then prove the fundamental lemma
for every well-typed term and reducible closing substitution.

[sf-norm]: https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ : List (Ty Base)}

namespace Steps

/-- **Multi-step evaluation is a congruence in function position.** Let $f$ and $f'$ be terms
of type $A \Rightarrow B$ and let $a$ be a term of type $A$, all in the same context. If $f$
evaluates to $f'$ in zero or more call-by-value steps, then the application $f\,a$ evaluates
to $f'\,a$ in zero or more steps. -/
theorem appFun {f f' : Tm Γ (A ⇒ B)} (a : Tm Γ A) (h : Steps f f') :
    Steps (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (.appFun hstep)

/-- **Evaluating the argument of a value function is a multi-step congruence.** Let $f$ be a term
of type $A \Rightarrow B$ and let $a$, $a'$ be terms of type $A$, all in the same context. If $f$
is a value and $a$ evaluates to $a'$ in zero or more call-by-value steps, then the application
$f\,a$ evaluates to $f\,a'$ in zero or more steps. -/
theorem appArg {a a' : Tm Γ A} {f : Tm Γ (A ⇒ B)} (hv : Value f) (h : Steps a a') :
    Steps (.app f a) (.app f a') := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (.appArg hv hstep)

/-- **Evaluation to a value passes through every reduct.** Let $t$, $t'$ and $v$ be terms of the
same type in the same context, with $v$ a value. If $t$ evaluates to $v$ and $t$ evaluates to
$t'$, each in finitely many call-by-value steps, then $t'$ evaluates to $v$ in finitely many
steps.

The value endpoint makes the first evaluation maximal, so every other finite
evaluation is one of its prefixes. -/
theorem suffix_of_value {t t' v : Tm Γ A} (htv : Steps t v) (hv : Value v)
    (htt' : Steps t t') : Steps t' v := by
  induction htv using Relation.ReflTransGen.head_induction_on generalizing t' with
  | refl =>
      cases htt' using Relation.ReflTransGen.head_induction_on with
      | refl => exact .refl
      | head hstep _ _ => exact (Step.value_irreducible hv hstep).elim
  | @head t middle hstep hrest ih =>
      cases htt' using Relation.ReflTransGen.head_induction_on with
      | refl => exact (Relation.ReflTransGen.single hstep).trans hrest
      | @head _ middle' hstep' hrest' =>
          have hmiddle : middle = middle' := Step.deterministic hstep hstep'
          subst middle'
          exact ih hrest'

end Steps

/-- **Termination of closed terms.** A closed term $t$ terminates when it evaluates, in
finitely many call-by-value steps, to a value. -/
def Terminates (t : Tm [] A) : Prop := ∃ v, Steps t v ∧ Value v

namespace Terminates

/-- **Values terminate.** Every closed term of the simply typed lambda calculus that is a value
terminates.

No evaluation step is needed: the value itself is the value reached. -/
theorem of_value {v : Tm [] A} (hv : Value v) : Terminates v := ⟨v, .refl, hv⟩

/-- **Termination is closed under backward evaluation.** Let $t$ and $t'$ be closed terms of
the same type. If $t$ evaluates to $t'$ in zero or more call-by-value steps and $t'$
terminates, then $t$ terminates. -/
theorem anti {t t' : Tm [] A} (h : Steps t t') (ht' : Terminates t') : Terminates t := by
  rcases ht' with ⟨v, ht'v, hv⟩
  exact ⟨v, h.trans ht'v, hv⟩

/-- **Termination is closed under forward evaluation.** Let $t$ and $t'$ be closed terms of
the same type. If $t$ terminates and $t$ evaluates to $t'$ in zero or more call-by-value
steps, then $t'$ terminates. -/
theorem forward {t t' : Tm [] A} (ht : Terminates t) (h : Steps t t') : Terminates t' := by
  rcases ht with ⟨v, htv, hv⟩
  exact ⟨v, Steps.suffix_of_value htv hv h, hv⟩

end Terminates

/-- **Tait reducibility for closed terms.** Reducibility of a closed term $t$ is defined by
recursion on its simple type. At a base type, $t$ is reducible when it terminates. At a function
type $A \Rightarrow B$, $t$ is reducible when it terminates and, for every reducible closed term
$a$ of type $A$, the application $t\,a$ is reducible.
-/
def Reducible : {A : Ty Base} → Tm [] A → Prop
  | .base _, t => Terminates t
  | .arr A _B, f =>
      Terminates f ∧ ∀ (a : Tm [] A), Reducible a → Reducible (.app f a)

namespace Reducible

/-- **Reducible terms terminate.** Every reducible closed term of the simply typed lambda
calculus terminates. -/
theorem terminates : {A : Ty Base} → {t : Tm [] A} → Reducible t → Terminates t
  | .base _, _, ht => ht
  | .arr _ _B, _, hf => hf.1

/-- **Reducibility is closed under forward evaluation.** Let $t$ and $t'$ be closed terms of
the same type. If $t$ is reducible and $t$ evaluates to $t'$ in zero or more call-by-value
steps, then $t'$ is reducible. -/
theorem forward : {A : Ty Base} → {t t' : Tm [] A} →
    Steps t t' → Reducible t → Reducible t'
  | .base _, _, _, h, ht => Terminates.forward ht h
  | .arr A B, f, f', h, hf => by
      refine ⟨hf.1.forward h, ?_⟩
      intro a ha
      exact forward (A := B) (Steps.appFun a h) (hf.2 a ha)
termination_by A => sizeOf A

/-- **Reducibility is closed under backward evaluation.** Let $t$ and $t'$ be closed terms of
the same type. If $t$ evaluates to $t'$ in zero or more call-by-value steps and $t'$ is
reducible, then $t$ is reducible. -/
theorem anti : {A : Ty Base} → {t t' : Tm [] A} →
    Steps t t' → Reducible t' → Reducible t
  | .base _, _, _, h, ht' => Terminates.anti h ht'
  | .arr A B, f, f', h, hf' => by
      refine ⟨hf'.1.anti h, ?_⟩
      intro a ha
      exact anti (A := B) (Steps.appFun a h) (hf'.2 a ha)
termination_by A => sizeOf A

/-- **Reducibility is invariant under evaluation.** Let $t$ and $t'$ be closed terms of the
same type. If $t$ evaluates to $t'$ in zero or more call-by-value steps, then $t$ is reducible
if and only if $t'$ is reducible. -/
theorem iff_of_steps {t t' : Tm [] A} (h : Steps t t') : Reducible t ↔ Reducible t' :=
  ⟨forward h, anti h⟩

end Reducible

/-- **Reducible substitutions.** A substitution $\sigma$ that replaces each variable of a
context $\Gamma$ by a closed term of the same type is reducible when $\sigma(x)$ is reducible
for every variable $x$ of $\Gamma$. -/
def ReducibleSub (σ : Sub Γ []) : Prop := ∀ {A} (x : Var Γ A), Reducible (σ x)

namespace ReducibleSub

/-- **Substitutions on the empty context are reducible.** Every substitution from the empty
context to closed terms is reducible, since the empty context has no variables. -/
theorem empty (σ : Sub ([] : List (Ty Base)) []) : ReducibleSub σ := by
  intro A x
  nomatch x

/-- **Extending a reducible substitution by a reducible term keeps it reducible.** Let $\sigma$
be a substitution that sends each variable of a context $\Gamma$ to a closed term of the same
type, and let $a$ be a closed term of type $A$. If $\sigma$ and $a$ are reducible, then so is
the substitution on the context $A, \Gamma$ that sends the newest variable to $a$ and each
older variable $x$ to $\sigma(x)$. -/
theorem cons {σ : Sub Γ []} (hσ : ReducibleSub σ) {a : Tm [] A} (ha : Reducible a) :
    ReducibleSub (Sub.cons a σ) := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact hσ x

end ReducibleSub

/-- **Fundamental theorem of the reducibility relation.** Let $t$ be a term of type $A$ in a
context $\Gamma$, and let $\sigma$ be a reducible substitution sending each variable of $\Gamma$
to a closed term of the same type. Then the closed term obtained by applying $\sigma$ to $t$ is
reducible.

The lambda case is the key: evaluate an arbitrary reducible
argument to a value, cross the beta step, and invoke the induction hypothesis
under the extended substitution. -/
theorem fundamental (t : Tm Γ A) (σ : Sub Γ []) (hσ : ReducibleSub σ) :
    Reducible (Tm.subst σ t) := by
  induction t with
  | var x => exact hσ x
  | app f a ihf iha => exact (ihf σ hσ).2 _ (iha σ hσ)
  | @lam A B Γ body ih =>
      refine ⟨Terminates.of_value (.lam _), ?_⟩
      intro a ha
      rcases ha.terminates with ⟨v, hav, hv⟩
      have hvReducible : Reducible v := ha.forward hav
      have harg : Steps
          (.app (.lam (Tm.subst (Sub.lift σ) body)) a)
          (.app (.lam (Tm.subst (Sub.lift σ) body)) v) :=
        Steps.appArg (.lam _) hav
      have hbeta : Step
          (.app (.lam (Tm.subst (Sub.lift σ) body)) v)
          (Tm.instantiate (Tm.subst (Sub.lift σ) body) v) := .beta hv
      apply Reducible.anti (harg.tail hbeta)
      rw [← Tm.subst_cons]
      exact ih (Sub.cons v σ) (hσ.cons hvReducible)

/-- **Closed terms are reducible.** Every closed well-typed term of the simply typed lambda
calculus is reducible. -/
theorem reducible_closed (t : Tm [] A) : Reducible t := by
  rw [← Tm.subst_id t]
  exact fundamental t Sub.id (ReducibleSub.empty Sub.id)

/-- **Termination of the call-by-value simply typed lambda calculus.** Every closed well-typed
term evaluates, in finitely many call-by-value steps, to a value. -/
theorem terminates_closed (t : Tm [] A) : Terminates t := (reducible_closed t).terminates

end Cslib.Languages.LambdaCalculus.Stlc
