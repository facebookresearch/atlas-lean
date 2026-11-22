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

/-- Multi-step evaluation is closed under the function position of an application. -/
theorem appFun {f f' : Tm Γ (A ⇒ B)} (a : Tm Γ A) (h : Steps f f') :
    Steps (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (.appFun hstep)

/-- Once the function is a value, multi-step evaluation is closed under the argument position. -/
theorem appArg {a a' : Tm Γ A} {f : Tm Γ (A ⇒ B)} (hv : Value f) (h : Steps a a') :
    Steps (.app f a) (.app f a') := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (.appArg hv hstep)

/-- Two evaluations from the same term agree until one of them stops.

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

/-- A closed term terminates when call-by-value evaluation reaches a value. -/
def Terminates (t : Tm [] A) : Prop := ∃ v, Steps t v ∧ Value v

namespace Terminates

/-- Values terminate without taking a step. -/
theorem of_value {v : Tm [] A} (hv : Value v) : Terminates v := ⟨v, .refl, hv⟩

/-- Termination is preserved by adding an evaluation prefix. -/
theorem anti {t t' : Tm [] A} (h : Steps t t') (ht' : Terminates t') : Terminates t := by
  rcases ht' with ⟨v, ht'v, hv⟩
  exact ⟨v, h.trans ht'v, hv⟩

/-- Termination is preserved by taking evaluation steps. -/
theorem forward {t t' : Tm [] A} (ht : Terminates t) (h : Steps t t') : Terminates t' := by
  rcases ht with ⟨v, htv, hv⟩
  exact ⟨v, Steps.suffix_of_value htv hv h, hv⟩

end Terminates

/-- Tait reducibility for closed terms.

At a base type, reducibility is termination.  At a function type, a reducible
term terminates and maps every reducible argument to a reducible application.
-/
def Reducible : {A : Ty Base} → Tm [] A → Prop
  | .base _, t => Terminates t
  | .arr A _B, f =>
      Terminates f ∧ ∀ (a : Tm [] A), Reducible a → Reducible (.app f a)

namespace Reducible

/-- Every reducible term terminates. -/
theorem terminates : {A : Ty Base} → {t : Tm [] A} → Reducible t → Terminates t
  | .base _, _, ht => ht
  | .arr _ _B, _, hf => hf.1

/-- Reducibility is preserved by taking evaluation steps. -/
theorem forward : {A : Ty Base} → {t t' : Tm [] A} →
    Steps t t' → Reducible t → Reducible t'
  | .base _, _, _, h, ht => Terminates.forward ht h
  | .arr A B, f, f', h, hf => by
      refine ⟨hf.1.forward h, ?_⟩
      intro a ha
      exact forward (A := B) (Steps.appFun a h) (hf.2 a ha)
termination_by A => sizeOf A

/-- Reducibility is preserved by adding an evaluation prefix. -/
theorem anti : {A : Ty Base} → {t t' : Tm [] A} →
    Steps t t' → Reducible t' → Reducible t
  | .base _, _, _, h, ht' => Terminates.anti h ht'
  | .arr A B, f, f', h, hf' => by
      refine ⟨hf'.1.anti h, ?_⟩
      intro a ha
      exact anti (A := B) (Steps.appFun a h) (hf'.2 a ha)
termination_by A => sizeOf A

/-- Reducibility is invariant under multi-step evaluation. -/
theorem iff_of_steps {t t' : Tm [] A} (h : Steps t t') : Reducible t ↔ Reducible t' :=
  ⟨forward h, anti h⟩

end Reducible

/-- A closing substitution is reducible when every one of its images is reducible. -/
def ReducibleSub (σ : Sub Γ []) : Prop := ∀ {A} (x : Var Γ A), Reducible (σ x)

namespace ReducibleSub

/-- The empty context has a unique reducible substitution. -/
theorem empty (σ : Sub ([] : List (Ty Base)) []) : ReducibleSub σ := by
  intro A x
  nomatch x

/-- Extend a reducible substitution by a reducible image for the newest variable. -/
theorem cons {σ : Sub Γ []} (hσ : ReducibleSub σ) {a : Tm [] A} (ha : Reducible a) :
    ReducibleSub (Sub.cons a σ) := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact hσ x

end ReducibleSub

/-- The fundamental theorem of the logical relation.

Substituting reducible closed terms for all free variables produces a reducible
closed term.  The lambda case is the key: evaluate an arbitrary reducible
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

/-- Every closed well-typed term is reducible. -/
theorem reducible_closed (t : Tm [] A) : Reducible t := by
  rw [← Tm.subst_id t]
  exact fundamental t Sub.id (ReducibleSub.empty Sub.id)

/-- Every closed well-typed term evaluates to a value. -/
theorem terminates_closed (t : Tm [] A) : Terminates t := (reducible_closed t).terminates

end Cslib.Languages.LambdaCalculus.Stlc
