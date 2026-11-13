/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import MathlibExt.Algebra.AffineRecurrence
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Expectations-augmented Phillips curve

Adaptive expectations (`πe (t + 1) = π t`) substituted into the expectations-augmented
Phillips curve give the recurrence `π (t + 1) = π t - κ * (u (t + 1) - uₙ)`. At the
natural rate inflation is constant; with a constant unemployment gap inflation moves
linearly. A model-definition consistency lemma, not empirical validation.

## Main results

* `MathlibExt.Economics.Macro.PhillipsCurve.phillips_recurrence`: the recurrence.
* `MathlibExt.Economics.Macro.PhillipsCurve.phillips_natural_rate`: constant at natural rate.
* `MathlibExt.Economics.Macro.PhillipsCurve.phillips_acceleration`: constant-gap closed form.
-/

namespace MathlibExt.Economics.Macro.PhillipsCurve

/-- Adaptive expectations: expected inflation next period equals actual inflation this
period, `πe (t + 1) = π t`. -/
def AdaptiveExpectations (πe π : ℕ → ℝ) : Prop :=
  ∀ t, πe (t + 1) = π t

/-- Expectations-augmented Phillips curve: next period's inflation equals expected
inflation minus `κ` times the unemployment gap `u (t + 1) - uₙ`, where `κ` is the
Phillips-curve slope and `uₙ` the natural rate of unemployment. -/
def IsPhillipsCurve (π πe u : ℕ → ℝ) (κ uₙ : ℝ) : Prop :=
  ∀ t, π (t + 1) = πe (t + 1) - κ * (u (t + 1) - uₙ)

/-- **Phillips-curve recurrence (MA06.T03).** Substituting the stated adaptive-expectation
rule into the stated Phillips curve yields the recurrence
`π (t + 1) = π t - κ * (u (t + 1) - uₙ)`. This is a model-definition consistency lemma;
it does not validate the Phillips curve empirically. -/
theorem phillips_recurrence {π πe u : ℕ → ℝ} {κ uₙ : ℝ}
    (hexp : AdaptiveExpectations πe π) (hpc : IsPhillipsCurve π πe u κ uₙ) :
    ∀ t, π (t + 1) = π t - κ * (u (t + 1) - uₙ) := by
  intro t
  rw [hpc t, hexp t]

/-- **Natural rate (MA06.T03).** If unemployment stays at the natural rate, inflation is
constant from period to period. -/
theorem phillips_natural_rate {π πe u : ℕ → ℝ} {κ uₙ : ℝ}
    (hexp : AdaptiveExpectations πe π) (hpc : IsPhillipsCurve π πe u κ uₙ)
    (hnat : ∀ t, u t = uₙ) : ∀ t, π (t + 1) = π t := by
  intro t
  have h := phillips_recurrence hexp hpc t
  rw [hnat _, sub_self, mul_zero, sub_zero] at h
  exact h

/-- **Accelerationist form (MA06.T03).** If the unemployment gap is constant,
`u (t + 1) - uₙ = g` for every `t`, then inflation falls (or rises) linearly:
`π t = π 0 - t * (κ * g)`. Inflation is then a unit-root affine recurrence, so this is
`MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_add_nsmul_of_one` with intercept `-(κ * g)`. -/
theorem phillips_acceleration {π πe u : ℕ → ℝ} {κ uₙ g : ℝ}
    (hexp : AdaptiveExpectations πe π) (hpc : IsPhillipsCurve π πe u κ uₙ)
    (hgap : ∀ t, u (t + 1) - uₙ = g) : ∀ t, π t = π 0 - (t : ℝ) * (κ * g) := by
  have hrec : MathlibExt.AffineRecurrence.IsAffineRecurrence 1 (-(κ * g)) π := by
    intro n
    rw [phillips_recurrence hexp hpc n, hgap n]
    ring
  intro t
  rw [hrec.eq_add_nsmul_of_one t]
  ring

end MathlibExt.Economics.Macro.PhillipsCurve
