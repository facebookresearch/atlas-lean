/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCF: small-step call-by-name evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.PCF.BigStep
public import Mathlib.Logic.Relation

/-!
# Small-step call-by-name evaluation

`Step t t'` is the call-by-name reduction of closed PCF terms (Plotkin 1977,
the operational semantics of PCF; Streicher 2006): reduce the function of an
application, contract a β-redex without evaluating its argument, reduce the
argument of `succ` and `pred` and the test of `ifz`, compute `pred` and `ifz`
on numerals, and unfold `fix t` to `t (fix t)`.

The file proves that values are normal forms (`Value.not_step`), that the
relation is deterministic (`Step.deterministic`), and that it agrees with the
big-step semantics of `BigStep.lean`: `t ⇓ v` exactly when `t` reduces to the
value `v` in finitely many steps (`eval_iff_steps`).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF

open scoped CslibStlc

namespace Tm

/-- One step of call-by-name reduction of closed terms. -/
inductive Step : {A : Ty} → Tm [] A → Tm [] A → Prop
  | appLeft {A B : Ty} {f f' : Tm [] (A ⇒ B)} {a : Tm [] A} (h : Step f f') :
      Step (.app f a) (.app f' a)
  | beta {A B : Ty} {body : Tm [A] B} {a : Tm [] A} :
      Step (.app (.lam body) a) (body.instantiate a)
  | succ {t t' : Tm [] .nat} (h : Step t t') : Step (.succ t) (.succ t')
  | pred {t t' : Tm [] .nat} (h : Step t t') : Step (.pred t) (.pred t')
  | predZero : Step (.pred .zero) .zero
  | predSucc (n : Nat) : Step (.pred (numeral (n + 1))) (numeral n)
  | ifz {t t' s₁ s₂ : Tm [] .nat} (h : Step t t') : Step (.ifz t s₁ s₂) (.ifz t' s₁ s₂)
  | ifzZero {s₁ s₂ : Tm [] .nat} : Step (.ifz .zero s₁ s₂) s₁
  | ifzSucc (n : Nat) {s₁ s₂ : Tm [] .nat} : Step (.ifz (numeral (n + 1)) s₁ s₂) s₂
  | fix {A : Ty} {t : Tm [] (A ⇒ A)} : Step (.fix t) (.app t (.fix t))

/-- Reduction in any number of steps. -/
abbrev Steps {A : Ty} : Tm [] A → Tm [] A → Prop := Relation.ReflTransGen Step

/-- Numerals are normal forms. -/
theorem numeral_not_step (n : Nat) {t' : Tm [] .nat} : ¬ Step (numeral n) t' := by
  induction n generalizing t' with
  | zero => intro h; cases h
  | succ n ih =>
      intro h
      cases h with
      | succ h' => exact ih h'

/-- Values are normal forms. -/
theorem Value.not_step {A : Ty} {v t' : Tm [] A} (hv : v.Value) : ¬ Step v t' := by
  cases hv with
  | lam => intro h; cases h
  | numeral n => exact numeral_not_step n

theorem step_pred_numeral_succ {n : Nat} {t : Tm [] .nat}
    (h : Step (.pred (numeral (n + 1))) t) : t = numeral n := by
  generalize hx : (numeral (n + 1) : Tm [] .nat) = x at h
  cases h with
  | pred h' => subst hx; exact absurd h' (numeral_not_step _)
  | predZero => simp [numeral] at hx
  | predSucc m =>
      obtain rfl : n = m := by have := numeral_injective hx; omega
      rfl

theorem step_ifz_numeral_succ {n : Nat} {s₁ s₂ t : Tm [] .nat}
    (h : Step (.ifz (numeral (n + 1)) s₁ s₂) t) : t = s₂ := by
  generalize hx : (numeral (n + 1) : Tm [] .nat) = x at h
  cases h with
  | ifz h' => subst hx; exact absurd h' (numeral_not_step _)
  | ifzZero => simp [numeral] at hx
  | ifzSucc m => rfl

/-- Reduction is deterministic. -/
theorem Step.deterministic {A : Ty} {t t₁ t₂ : Tm [] A} (h₁ : Step t t₁) (h₂ : Step t t₂) :
    t₁ = t₂ := by
  induction h₁ with
  | appLeft h ih =>
      cases h₂ with
      | appLeft h' => rw [ih h']
      | beta => exact absurd h (Value.not_step (.lam _))
  | beta =>
      cases h₂ with
      | appLeft h' => exact absurd h' (Value.not_step (.lam _))
      | beta => rfl
  | succ h ih =>
      cases h₂ with
      | succ h' => rw [ih h']
  | pred h ih =>
      cases h₂ with
      | pred h' => rw [ih h']
      | predZero => exact absurd h (numeral_not_step 0)
      | predSucc n => exact absurd h (numeral_not_step (n + 1))
  | predZero =>
      cases h₂ with
      | pred h' => exact absurd h' (numeral_not_step 0)
      | predZero => rfl
  | predSucc n => exact (step_pred_numeral_succ h₂).symm
  | ifz h ih =>
      cases h₂ with
      | ifz h' => rw [ih h']
      | ifzZero => exact absurd h (numeral_not_step 0)
      | ifzSucc n => exact absurd h (numeral_not_step (n + 1))
  | ifzZero =>
      cases h₂ with
      | ifz h' => exact absurd h' (numeral_not_step 0)
      | ifzZero => rfl
  | ifzSucc n => exact (step_ifz_numeral_succ h₂).symm
  | fix =>
      cases h₂ with
      | fix => rfl

namespace Steps

theorem appLeft {A B : Ty} {f f' : Tm [] (A ⇒ B)} {a : Tm [] A} (h : Steps f f') :
    Steps (.app f a) (.app f' a) :=
  Relation.ReflTransGen.lift (fun f => Tm.app f a) (fun _ _ h => Step.appLeft h) _ _ h

theorem succ {t t' : Tm [] .nat} (h : Steps t t') : Steps (.succ t) (.succ t') :=
  Relation.ReflTransGen.lift Tm.succ (fun _ _ h => Step.succ h) _ _ h

theorem pred {t t' : Tm [] .nat} (h : Steps t t') : Steps (.pred t) (.pred t') :=
  Relation.ReflTransGen.lift Tm.pred (fun _ _ h => Step.pred h) _ _ h

theorem ifz {t t' s₁ s₂ : Tm [] .nat} (h : Steps t t') :
    Steps (.ifz t s₁ s₂) (.ifz t' s₁ s₂) :=
  Relation.ReflTransGen.lift (fun t => Tm.ifz t s₁ s₂) (fun _ _ h => Step.ifz h) _ _ h

end Steps

/-- Big-step evaluation is reduction to a value. -/
theorem Eval.steps {A : Ty} {t v : Tm [] A} (h : Eval t v) : Steps t v := by
  induction h with
  | lam => exact .refl
  | zero => exact .refl
  | succ _ ih => exact Steps.succ ih
  | predZero _ ih => exact (Steps.pred ih).tail .predZero
  | predSucc _ ih => exact (Steps.pred ih).tail (.predSucc _)
  | ifzZero _ _ iht ihs => exact ((Steps.ifz iht).tail .ifzZero).trans ihs
  | ifzSucc _ _ iht ihs => exact ((Steps.ifz iht).tail (.ifzSucc _)).trans ihs
  | app _ _ ihf ihb => exact ((Steps.appLeft ihf).tail .beta).trans ihb
  | fix _ ih => exact Relation.ReflTransGen.head .fix ih

/-- A step backwards preserves big-step evaluation. -/
theorem Step.eval {A : Ty} {t t' v : Tm [] A} (hstep : Step t t') (heval : Eval t' v) :
    Eval t v := by
  induction hstep with
  | appLeft _ ih =>
      cases heval with
      | app hf hb => exact .app (ih hf) hb
  | beta => exact .app .lam heval
  | succ _ ih =>
      cases heval with
      | succ h => exact .succ (ih h)
  | pred _ ih =>
      cases heval with
      | predZero h => exact .predZero (ih h)
      | predSucc h => exact .predSucc (ih h)
  | predZero =>
      cases heval
      exact .predZero .zero
  | predSucc n =>
      rw [← Eval.deterministic (Eval.numeral n) heval]
      exact .predSucc (Eval.numeral (n + 1))
  | ifz _ ih =>
      cases heval with
      | ifzZero ht hs => exact .ifzZero (ih ht) hs
      | ifzSucc ht hs => exact .ifzSucc (ih ht) hs
  | ifzZero => exact .ifzZero .zero heval
  | ifzSucc n => exact .ifzSucc (Eval.numeral (n + 1)) heval
  | fix => exact .fix heval

/-- Reduction to a value is big-step evaluation. -/
theorem Steps.eval {A : Ty} {t v : Tm [] A} (h : Steps t v) (hv : v.Value) : Eval t v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Eval.of_value hv
  | head hstep _ ih => exact hstep.eval ih

/-- Big-step evaluation coincides with reduction to a value. -/
theorem eval_iff_steps {A : Ty} {t v : Tm [] A} : Eval t v ↔ Steps t v ∧ v.Value :=
  ⟨fun h => ⟨h.steps, h.value⟩, fun ⟨h, hv⟩ => h.eval hv⟩

end Tm

end Cslib.Languages.LambdaCalculus.PCF
