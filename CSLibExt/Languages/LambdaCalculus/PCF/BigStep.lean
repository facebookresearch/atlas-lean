/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCF: big-step call-by-name evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.PCF.Syntax

/-!
# Call-by-name big-step evaluation

`Eval t v` is the big-step call-by-name evaluation of closed PCF terms
(Streicher, *Domain-Theoretic Foundations of Functional Programming*, the
operational semantics of PCF): values are abstractions and numerals, an
application substitutes its unevaluated argument, the zero test and the
arithmetic operations evaluate their numeric argument, and `fix t` evaluates
as `t (fix t)`.

The file proves that results are values (numerals at the ground type), that
values evaluate to themselves, and that evaluation is deterministic.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF

open scoped CslibStlc

namespace Tm

/-- Closed values: abstractions and numerals. -/
inductive Value : {A : Ty} → Tm [] A → Prop
  | lam {A B : Ty} (body : Tm [A] B) : Value (.lam body)
  | numeral (n : Nat) : Value (numeral n)

/-- Closed values of ground type are numerals. -/
theorem Value.eq_numeral {v : Tm [] .nat} (hv : v.Value) : ∃ n, v = Tm.numeral n := by
  cases hv with
  | numeral n => exact ⟨n, rfl⟩

/-- Big-step call-by-name evaluation of closed terms. -/
inductive Eval : {A : Ty} → Tm [] A → Tm [] A → Prop
  | lam {A B : Ty} {body : Tm [A] B} : Eval (.lam body) (.lam body)
  | zero : Eval .zero .zero
  | succ {t : Tm [] .nat} {n : Nat} (h : Eval t (numeral n)) :
      Eval (.succ t) (numeral (n + 1))
  | predZero {t : Tm [] .nat} (h : Eval t .zero) : Eval (.pred t) .zero
  | predSucc {t : Tm [] .nat} {n : Nat} (h : Eval t (numeral (n + 1))) :
      Eval (.pred t) (numeral n)
  | ifzZero {t s₁ s₂ v : Tm [] .nat} (ht : Eval t .zero) (hs : Eval s₁ v) :
      Eval (.ifz t s₁ s₂) v
  | ifzSucc {t s₁ s₂ v : Tm [] .nat} {n : Nat} (ht : Eval t (numeral (n + 1)))
      (hs : Eval s₂ v) : Eval (.ifz t s₁ s₂) v
  | app {A B : Ty} {f : Tm [] (A ⇒ B)} {a : Tm [] A} {body : Tm [A] B} {v : Tm [] B}
      (hf : Eval f (.lam body)) (hb : Eval (body.instantiate a) v) : Eval (.app f a) v
  | fix {A : Ty} {t : Tm [] (A ⇒ A)} {v : Tm [] A}
      (h : Eval (.app t (.fix t)) v) : Eval (.fix t) v

namespace Eval

/-- Numerals evaluate to themselves. -/
theorem numeral (n : Nat) : Eval (Tm.numeral n) (Tm.numeral n) := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .succ ih

/-- Values evaluate to themselves. -/
theorem of_value {A : Ty} {v : Tm [] A} (hv : v.Value) : Eval v v := by
  cases hv with
  | lam => exact .lam
  | numeral n => exact numeral n

/-- Evaluation results are values. -/
theorem value {A : Ty} {t v : Tm [] A} (h : Eval t v) : v.Value := by
  induction h with
  | lam => exact .lam _
  | zero => exact .numeral 0
  | succ _ _ => exact .numeral _
  | predZero _ _ => exact .numeral 0
  | predSucc _ _ => exact .numeral _
  | ifzZero _ _ _ ih => exact ih
  | ifzSucc _ _ _ ih => exact ih
  | app _ _ _ ih => exact ih
  | fix _ ih => exact ih

/-- Evaluation is deterministic. -/
theorem deterministic {A : Ty} {t v w : Tm [] A} (hv : Eval t v) (hw : Eval t w) : v = w := by
  induction hv with
  | lam => cases hw; rfl
  | zero => cases hw; rfl
  | succ _ ih =>
      cases hw with
      | succ h' => rw [Tm.numeral_injective (ih h')]
  | predZero _ ih =>
      cases hw with
      | predZero _ => rfl
      | predSucc h' => exact absurd (ih h') (by simp [Tm.numeral])
  | predSucc _ ih =>
      cases hw with
      | predZero h' => exact absurd (ih h') (by simp [Tm.numeral])
      | predSucc h' =>
          have := Tm.numeral_injective (ih h')
          rw [Nat.succ.inj this]
  | ifzZero _ _ iht ihs =>
      cases hw with
      | ifzZero _ hs' => exact ihs hs'
      | ifzSucc ht' _ => exact absurd (iht ht') (by simp [Tm.numeral])
  | ifzSucc _ _ iht ihs =>
      cases hw with
      | ifzZero ht' _ => exact absurd (iht ht') (by simp [Tm.numeral])
      | ifzSucc _ hs' => exact ihs hs'
  | app _ _ ihf ihb =>
      cases hw with
      | app hf' hb' =>
          cases ihf hf'
          exact ihb hb'
  | fix _ ih =>
      cases hw with
      | fix h' => exact ih h'

end Eval

end Tm

end Cslib.Languages.LambdaCalculus.PCF
