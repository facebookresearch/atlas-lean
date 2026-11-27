/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.StlcExtended.Semantics

/-!
# Tests for the call-by-value dynamics of the extended simply typed lambda calculus

Negative controls, each proved from the definitions alone:

* an open variable is neither a value nor reducible, so progress needs a closed term;
* pairs are eager: a pair whose left component reduces is not a value, and its only step is in
  the left component;
* application is left to right: while the function position reduces, the argument is not
  reduced, even when it can be;
* nothing reduces under a lambda, even a body that contains a redex;
* a conditional does not evaluate its branches;
* `let` is by value: the bound term is reduced before it is substituted;
* `Tm.fst` accepts only terms of product type, so `Tm.fst Tm.unit` does not elaborate;
* no value has a base type.

Statement pins restate every theorem of the semantics and are closed by applying the theorem
itself, so a weakened or drifted statement fails here.
-/

@[expose] public section

universe u

namespace Cslib.Languages.LambdaCalculus.StlcExtended.SemanticsTests

open Cslib.Languages.LambdaCalculus.StlcExtended
open scoped CslibStlcExtended

/-- The boolean identity. -/
def idB : Tm (Base := Unit) [] (.bool ⇒ .bool) := .lam (.var .zero)

/-- The constant function on booleans that returns its first argument. -/
def constB : Tm (Base := Unit) [] (.bool ⇒ .bool ⇒ .bool) := .lam (.lam (.var (.succ .zero)))

/-! ### Single steps -/

example : Step (.app idB .tt) .tt := .beta .tt

example : Step (.fst (.pair .tt .unit) : Tm (Base := Unit) [] .bool) .tt := .fstPair .tt .unit

example : Step (.snd (.pair .tt .unit) : Tm (Base := Unit) [] .unit) .unit := .sndPair .tt .unit

example : Step (.case (.inr (A := .unit) .ff) .tt (.var .zero) : Tm (Base := Unit) [] .bool) .ff :=
  .caseInr .ff

example : Step (.case (.inl (B := .bool) .unit) .tt (.var .zero) : Tm (Base := Unit) [] .bool)
    .tt :=
  .caseInl .unit

example : Step (.ite .ff .tt .ff : Tm (Base := Unit) [] .bool) .ff := .iteFf

example : Step (.letIn .unit .tt : Tm (Base := Unit) [] .bool) .tt := .letValue .unit

example : Step (.inl (.app idB .tt) : Tm (Base := Unit) [] (.sum .bool .unit)) (.inl .tt) :=
  .inl (.beta .tt)

example : Step (.pair .tt (.app idB .ff) : Tm (Base := Unit) [] (.prod .bool .bool))
    (.pair .tt .ff) :=
  .pairR .tt (.beta .ff)

/-! ### Negative controls -/

/-- An open variable is not a value. -/
theorem openVar_not_value : ¬ Value (.var .zero : Tm (Base := Unit) [.bool] .bool) := by
  intro h
  cases h

/-- An open variable does not reduce. -/
theorem openVar_normal (t' : Tm (Base := Unit) [.bool] .bool) : ¬ Step (.var .zero) t' := by
  intro h
  cases h

/-- Progress fails for open terms, so its restriction to closed terms is needed. -/
theorem progress_needs_closed :
    ¬ ∀ t : Tm (Base := Unit) [.bool] .bool, Value t ∨ ∃ t', Step t t' := by
  intro h
  rcases h (.var .zero) with hv | ⟨t', ht⟩
  · exact openVar_not_value hv
  · exact openVar_normal t' ht

/-- Pairs are eager: a pair whose left component reduces is not a value. -/
theorem eagerPair_not_value :
    ¬ Value (.pair (.app idB .tt) .ff : Tm (Base := Unit) [] (.prod .bool .bool)) := by
  intro h
  cases h with
  | pair ha _ => cases ha

/-- The pair reduces in its left component. -/
theorem eagerPair_step :
    Step (.pair (.app idB .tt) .ff : Tm (Base := Unit) [] (.prod .bool .bool)) (.pair .tt .ff) :=
  .pairL (.beta .tt)

/-- The left-component step is the only step of the pair. -/
theorem eagerPair_step_unique {t' : Tm (Base := Unit) [] (.prod .bool .bool)}
    (h : Step (.pair (.app idB .tt) .ff) t') : t' = .pair .tt .ff := by
  cases h with
  | pairL h' =>
    cases h' with
    | beta _ => rfl
    | appFun h'' => cases h''
    | appArg _ h'' => cases h''
  | pairR hv _ => cases hv

/-- Application is left to right: the function position steps first. -/
theorem leftToRight_step :
    Step (.app (.app constB .tt) (.app idB .ff) : Tm (Base := Unit) [] .bool)
      (.app (.lam .tt) (.app idB .ff)) :=
  .appFun (.beta .tt)

/-- While the function position reduces, the argument is not reduced, although it can be. -/
theorem leftToRight_step_unique {t' : Tm (Base := Unit) [] .bool}
    (h : Step (.app (.app constB .tt) (.app idB .ff)) t') :
    t' = .app (.lam .tt) (.app idB .ff) := by
  cases h with
  | appFun h' =>
    cases h' with
    | beta _ => rfl
    | appFun h'' => cases h''
    | appArg _ h'' => cases h''
  | appArg hv _ => cases hv

/-- The argument of the application above can reduce on its own. -/
example : Step (.app idB .ff) .ff := .beta .ff

/-- A lambda whose body contains a redex. -/
def underLam : Tm (Base := Unit) [] (.bool ⇒ .bool) := .lam (.app (.lam (.var .zero)) (.var .zero))

/-- Nothing reduces under a lambda: the abstraction is a value. -/
theorem underLam_value : Value underLam := .lam _

/-- Nothing reduces under a lambda: the abstraction is a normal form. -/
theorem underLam_normal : Step.NormalForm underLam := fun _ h => by cases h

/-- A term of type `unit` that reduces. -/
def reducibleUnit : Tm (Base := Unit) [] .unit := .app (.lam (.var .zero)) .unit

example : Step reducibleUnit .unit := .beta .unit

/-- A conditional selects its branch in one step without evaluating the branches. -/
theorem ite_branch_step : Step (.ite .tt .unit reducibleUnit) .unit := .iteTt

/-- Selecting the branch is the only step: the reducible else branch is not touched. -/
theorem ite_branch_step_unique {t' : Tm (Base := Unit) [] .unit}
    (h : Step (.ite .tt .unit reducibleUnit) t') : t' = .unit := by
  cases h with
  | iteTt => rfl
  | ite h' => cases h'

/-- The body of a `let` that tests its bound variable. -/
def letBody : Tm (Base := Unit) [.bool] .bool := .ite (.var .zero) .ff .tt

/-- `let` is by value: the bound term reduces first. -/
theorem letByValue_step : Step (.letIn (.app idB .tt) letBody) (.letIn .tt letBody) :=
  .letL (.beta .tt)

/-- Reducing the bound term is the only step: the unreduced term is not substituted. -/
theorem letByValue_step_unique {t' : Tm (Base := Unit) [] .bool}
    (h : Step (.letIn (.app idB .tt) letBody) t') : t' = .letIn .tt letBody := by
  cases h with
  | letL h' =>
    cases h' with
    | beta _ => rfl
    | appFun h'' => cases h''
    | appArg _ h'' => cases h''
  | letValue hv => cases hv

/-- Intrinsic typing rejects ill-typed terms: `Tm.fst` needs an argument of product type, so the
projection of the unit value does not elaborate. -/
example : True := by
  fail_if_success
    have _ := (Tm.fst Tm.unit : Tm (Base := Unit) [] .bool)
  trivial

/-- No value has a base type, so tests use the unit and boolean types. -/
theorem base_not_value (t : Tm (Base := Unit) [] (.base ())) : ¬ Value t := by
  intro h
  cases h

/-! ### Statement pins -/

section Pins

variable {Base : Type u} {A B C : Ty Base} {Γ : List (Ty Base)}

/-- Pin: a variable is not a value. -/
theorem not_var_pin (x : Var Γ A) : ¬ Value (.var x) := Value.not_var x

/-- Pin: an application is not a value. -/
theorem not_app_pin (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) : ¬ Value (.app f a) := Value.not_app f a

/-- Pin: a first projection is not a value. -/
theorem not_fst_pin (p : Tm Γ (.prod A B)) : ¬ Value (.fst p) := Value.not_fst p

/-- Pin: a second projection is not a value. -/
theorem not_snd_pin (p : Tm Γ (.prod A B)) : ¬ Value (.snd p) := Value.not_snd p

/-- Pin: a case analysis is not a value. -/
theorem not_case_pin (s : Tm Γ (.sum A B)) (l : Tm (A :: Γ) C) (r : Tm (B :: Γ) C) :
    ¬ Value (.case s l r) :=
  Value.not_case s l r

/-- Pin: a conditional is not a value. -/
theorem not_ite_pin (c : Tm Γ .bool) (t e : Tm Γ A) : ¬ Value (.ite c t e) :=
  Value.not_ite c t e

/-- Pin: a `let` is not a value. -/
theorem not_letIn_pin (a : Tm Γ A) (b : Tm (A :: Γ) B) : ¬ Value (.letIn a b) :=
  Value.not_letIn a b

/-- Pin: canonical forms at function types. -/
theorem closed_value_arr_pin {f : Tm [] (A ⇒ B)} (hv : Value f) :
    ∃ body : Tm [A] B, f = .lam body :=
  closed_value_arr hv

/-- Pin: canonical forms at product types. -/
theorem closed_value_prod_pin {p : Tm [] (.prod A B)} (hv : Value p) :
    ∃ (a : Tm [] A) (b : Tm [] B), Value a ∧ Value b ∧ p = .pair a b :=
  closed_value_prod hv

/-- Pin: canonical forms at sum types. -/
theorem closed_value_sum_pin {s : Tm [] (.sum A B)} (hv : Value s) :
    (∃ a : Tm [] A, Value a ∧ s = .inl a) ∨ (∃ b : Tm [] B, Value b ∧ s = .inr b) :=
  closed_value_sum hv

/-- Pin: canonical forms at the boolean type. -/
theorem closed_value_bool_pin {c : Tm (Base := Base) [] .bool} (hv : Value c) :
    c = .tt ∨ c = .ff :=
  closed_value_bool hv

/-- Pin: canonical forms at the unit type. -/
theorem closed_value_unit_pin {u : Tm (Base := Base) [] .unit} (hv : Value u) : u = .unit :=
  closed_value_unit hv

/-- Pin: values are irreducible. -/
theorem value_irreducible_pin {t t' : Tm Γ A} (hv : Value t) : ¬ Step t t' :=
  Step.value_irreducible hv

/-- Pin: progress for closed terms. -/
theorem progress_pin (t : Tm [] A) : Value t ∨ ∃ t', Step t t' := Step.progress t

/-- Pin: reduction is deterministic. -/
theorem deterministic_pin {t t₁ t₂ : Tm Γ A} (h₁ : Step t t₁) (h₂ : Step t t₂) : t₁ = t₂ :=
  Step.deterministic h₁ h₂

/-- Pin: normal forms are the normal forms of the step relation. -/
theorem normalForm_iff_normal_pin {t : Tm Γ A} :
    Step.NormalForm t ↔ Relation.Normal Step t :=
  Step.normalForm_iff_normal

/-- Pin: closed normal forms are exactly the values. -/
theorem closed_normalForm_iff_value_pin (t : Tm [] A) : Step.NormalForm t ↔ Value t :=
  Step.closed_normalForm_iff_value t

/-- Pin: a term reduces to at most one value. -/
theorem value_unique_pin {t v₁ v₂ : Tm Γ A} (h₁ : Steps t v₁) (h₂ : Steps t v₂)
    (hv₁ : Value v₁) (hv₂ : Value v₂) : v₁ = v₂ :=
  Steps.value_unique h₁ h₂ hv₁ hv₂

/-- Pin: multi-step reduction in the function of an application. -/
theorem steps_appFun_pin {f f' : Tm Γ (A ⇒ B)} {a : Tm Γ A} (h : Steps f f') :
    Steps (.app f a) (.app f' a) :=
  Steps.appFun h

/-- Pin: multi-step reduction in the argument of an application. -/
theorem steps_appArg_pin {f : Tm Γ (A ⇒ B)} {a a' : Tm Γ A} (hf : Value f) (h : Steps a a') :
    Steps (.app f a) (.app f a') :=
  Steps.appArg hf h

/-- Pin: multi-step reduction in the left component of a pair. -/
theorem steps_pairL_pin {a a' : Tm Γ A} {b : Tm Γ B} (h : Steps a a') :
    Steps (.pair a b) (.pair a' b) :=
  Steps.pairL h

/-- Pin: multi-step reduction in the right component of a pair. -/
theorem steps_pairR_pin {a : Tm Γ A} {b b' : Tm Γ B} (ha : Value a) (h : Steps b b') :
    Steps (.pair a b) (.pair a b') :=
  Steps.pairR ha h

/-- Pin: multi-step reduction in a first projection. -/
theorem steps_fst_pin {p p' : Tm Γ (.prod A B)} (h : Steps p p') :
    Steps (.fst p) (.fst p') :=
  Steps.fst h

/-- Pin: multi-step reduction in a second projection. -/
theorem steps_snd_pin {p p' : Tm Γ (.prod A B)} (h : Steps p p') :
    Steps (.snd p) (.snd p') :=
  Steps.snd h

/-- Pin: multi-step reduction in a left injection. -/
theorem steps_inl_pin {a a' : Tm Γ A} (h : Steps a a') :
    Steps (.inl a : Tm Γ (.sum A B)) (.inl a') :=
  Steps.inl h

/-- Pin: multi-step reduction in a right injection. -/
theorem steps_inr_pin {b b' : Tm Γ B} (h : Steps b b') :
    Steps (.inr b : Tm Γ (.sum A B)) (.inr b') :=
  Steps.inr h

/-- Pin: multi-step reduction in the scrutinee of a case analysis. -/
theorem steps_case_pin {s s' : Tm Γ (.sum A B)} {l : Tm (A :: Γ) C} {r : Tm (B :: Γ) C}
    (h : Steps s s') : Steps (.case s l r) (.case s' l r) :=
  Steps.case h

/-- Pin: multi-step reduction in the condition of a conditional. -/
theorem steps_ite_pin {c c' : Tm Γ .bool} {t e : Tm Γ A} (h : Steps c c') :
    Steps (.ite c t e) (.ite c' t e) :=
  Steps.ite h

/-- Pin: multi-step reduction in the bound term of a `let`. -/
theorem steps_letL_pin {a a' : Tm Γ A} {b : Tm (A :: Γ) B} (h : Steps a a') :
    Steps (.letIn a b) (.letIn a' b) :=
  Steps.letL h

end Pins

end Cslib.Languages.LambdaCalculus.StlcExtended.SemanticsTests
