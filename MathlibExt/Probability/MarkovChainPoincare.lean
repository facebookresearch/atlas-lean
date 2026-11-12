/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import MathlibExt.Probability.FiniteProbability

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Poincare contraction and variance decay

If a stationary Markov kernel contracts the `π`-variance of every
function by `(1 - gap)^2` in one step (a Poincare inequality in
variance form), then the variance of the `t`-step function
evolution decays like `(1 - gap)^(2t)`. This is the contraction
core of roadmap package ML-25 of the Atlas TCS canon roadmap;
spectral characterizations of the gap are follow-ups.

The mean and variance here are the shared
`MathlibExt.Probability.FiniteProbability.expectation` and
`.variance`, one kernel step is `Matrix.mulVec`, and iteration is
`Function.iterate` (see `applyKIter_eq_iterate`); `piMean`,
`piVar`, and `applyK` are names for those canonical operations,
not a second probability API.

Source: Levin and Peres, Markov Chains and Mixing Times (2017),
Chapter 12.
-/

open Finset

namespace MathlibExt.Probability.MarkovChainPoincare

/-- The `π`-mean of a function: the shared finite-probability
expectation. -/
noncomputable def piMean {α : Type*} [Fintype α] (π : α → ℝ) (f : α → ℝ) : ℝ :=
  MathlibExt.Probability.FiniteProbability.expectation π f

/-- The `π`-variance of a function: the shared finite-probability
variance. -/
noncomputable def piVar {α : Type*} [Fintype α] (π : α → ℝ) (f : α → ℝ) : ℝ :=
  MathlibExt.Probability.FiniteProbability.variance π f

/-- One step of the function evolution of a Markov kernel `K`
(rows indexed by the current state): `(applyK K f) x = ∑ y, K x y *
f y`. This is `Matrix.mulVec`. -/
noncomputable def applyK {α : Type*} [Fintype α] (K : α → α → ℝ) (f : α → ℝ) :
    α → ℝ :=
  Matrix.mulVec K f

/-- One kernel step, in sum form. -/
theorem applyK_apply {α : Type*} [Fintype α] (K : α → α → ℝ) (f : α → ℝ)
    (x : α) :
    applyK K f x = ∑ y, K x y * f y :=
  Matrix.mulVec_apply_eq_sum K f x

/-- Iterate of the function evolution. -/
noncomputable def applyKIter {α : Type*} [Fintype α] (K : α → α → ℝ) :
    ℕ → (α → ℝ) → α → ℝ
  | 0 => fun f => f
  | (t + 1) => fun f => applyK K (applyKIter K t f)

/-- Iteration is `Function.iterate` of one kernel step. -/
theorem applyKIter_eq_iterate {α : Type*} [Fintype α] (K : α → α → ℝ)
    (t : ℕ) (f : α → ℝ) :
    applyKIter K t f = (applyK K)^[t] f := by
  induction t with
  | zero => rfl
  | succ t ih =>
    calc applyKIter K (t + 1) f = applyK K (applyKIter K t f) := rfl
      _ = applyK K ((applyK K)^[t] f) := by rw [ih]
      _ = (applyK K)^[t + 1] f := (Function.iterate_succ_apply' _ _ _).symm

/-- Poincaré contraction implies exponential variance decay: if
`π` is stationary for the stochastic kernel `K`, the gap satisfies
`0 < gap ≤ 1` (so `(1 - gap)^2 < 1` is a genuine contraction
factor), and the kernel contracts the `π`-variance of every
function by the factor `(1 - gap)^2` in one step, then after `t`
steps the variance is at most `(1 - gap)^(2t)` times the initial
variance. -/
theorem piVar_decay {α : Type*} [Fintype α] {K : α → α → ℝ} {π : α → ℝ}
    {gap : ℝ}
    (hgap : 0 < gap ∧ gap ≤ 1)
    (hK_nonneg : ∀ x y, 0 ≤ K x y)
    (hK_sum : ∀ x, ∑ y, K x y = 1)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y)
    (hcontract : ∀ f : α → ℝ, piVar π (applyK K f) ≤ (1 - gap) ^ 2 * piVar π f)
    (f : α → ℝ) (t : ℕ) :
    piVar π (applyKIter K t f) ≤ ((1 - gap) ^ 2) ^ t * piVar π f := by
  have _hgap := hgap
  induction t with
  | zero => simp [applyKIter]
  | succ t ih =>
    have hnn : 0 ≤ (1 - gap) ^ 2 := sq_nonneg _
    have h1 := hcontract (applyKIter K t f)
    have h2 := mul_le_mul_of_nonneg_left ih hnn
    have h3 : (1 - gap) ^ 2 * (((1 - gap) ^ 2) ^ t * piVar π f)
        = ((1 - gap) ^ 2) ^ (t + 1) * piVar π f := by
      rw [pow_succ]; ring
    change piVar π (applyK K (applyKIter K t f)) ≤ _
    calc piVar π (applyK K (applyKIter K t f))
        ≤ (1 - gap) ^ 2 * piVar π (applyKIter K t f) := h1
      _ ≤ (1 - gap) ^ 2 * (((1 - gap) ^ 2) ^ t * piVar π f) := h2
      _ = ((1 - gap) ^ 2) ^ (t + 1) * piVar π f := h3

end MathlibExt.Probability.MarkovChainPoincare
