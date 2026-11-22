/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.PCF.SmallStep
public import CSLibExtTest.Languages.LambdaCalculus.PCF.BigStepTests

/-!
# Tests for small-step reduction in PCF

* Single steps: `pred 1 → 0`, `ifz 0 s₁ s₂ → s₁`, and `fix t → t (fix t)`.
* `fix (λx. zero)` reduces to `zero` in two steps.
* The big-step evaluations of `BigStepTests` become reduction sequences
  (`eval_iff_steps`), e.g. `countdown 1 →* zero`.
* `Ω := fix (λx : nat. x)` cycles through two terms and never reaches a value.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF.Tests

open scoped CslibStlc
open Tm

example : Step (.pred (numeral 1) : Tm [] .nat) .zero := .predSucc 0

example (s₁ s₂ : Tm [] .nat) : Step (.ifz .zero s₁ s₂) s₁ := .ifzZero

/-- `fix (λx. zero) →* zero` in two steps. -/
example : Steps fixZero .zero :=
  Relation.ReflTransGen.head .fix (Relation.ReflTransGen.single .beta)

/-- From big-step evaluation to reduction. -/
example : Steps (.app countdown (numeral 1)) .zero := countdown_one.steps

example : Steps ifzExample (numeral 1) := (eval_iff_steps.mp ifzExample_eval).1

/-- `Ω := fix (λx : nat. x)`. -/
def omegaS : Tm [] .nat := .fix (.lam (.var .zero))

/-- `Ω` reduces in two steps to itself. -/
example : Steps omegaS omegaS :=
  Relation.ReflTransGen.head .fix (Relation.ReflTransGen.single .beta)

/-- `Ω` never reaches a value: every term reachable from it is `Ω` or
`(λx. x) Ω`, and neither is a value. -/
example : ¬ ∃ v, Steps omegaS v ∧ v.Value := by
  rintro ⟨v, hsteps, hv⟩
  have key : ∀ u, Steps omegaS u → u = omegaS ∨ u = .app (.lam (.var .zero)) omegaS := by
    intro u hu
    induction hu with
    | refl => exact .inl rfl
    | tail _ hstep ih =>
        rcases ih with rfl | rfl
        · exact .inr (Step.deterministic hstep .fix)
        · exact .inl (Step.deterministic hstep .beta)
  rcases key v hsteps with rfl | rfl
  · exact Value.not_step hv .fix
  · exact Value.not_step hv .beta

end Cslib.Languages.LambdaCalculus.PCF.Tests
