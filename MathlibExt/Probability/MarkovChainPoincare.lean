/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

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

Source: Levin and Peres, Markov Chains and Mixing Times (2017),
Chapter 12.
-/

open Finset

/-- One step of the function evolution of a Markov kernel `K`
(rows indexed by the current state): `(applyK K f) x = ∑ y, K x y *
f y`. -/
noncomputable def applyK {α : Type*} [Fintype α] (K : α → α → ℝ) (f : α → ℝ) :
    α → ℝ :=
  fun x => ∑ y, K x y * f y

/-- Iterate of the function evolution. -/
noncomputable def applyKIter {α : Type*} [Fintype α] (K : α → α → ℝ) :
    ℕ → (α → ℝ) → α → ℝ
  | 0 => fun f => f
  | (t + 1) => fun f => applyK K (applyKIter K t f)

/-- The `π`-mean of a function. -/
noncomputable def piMean {α : Type*} [Fintype α] (π : α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ x, π x * f x

/-- The `π`-variance of a function. -/
noncomputable def piVar {α : Type*} [Fintype α] (π : α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ x, π x * (f x - piMean π f) ^ 2

/-- Poincaré contraction implies exponential variance decay: if
`π` is stationary for the stochastic kernel `K` and the kernel
contracts the `π`-variance of mean-centered functions by the factor
`(1 - gap)^2` in one step, then after `t` steps the variance is at
most `(1 - gap)^(2t)` times the initial variance. -/
theorem piVar_decay {α : Type*} [Fintype α] {K : α → α → ℝ} {π : α → ℝ}
    {gap : ℝ}
    (hK_nonneg : ∀ x y, 0 ≤ K x y)
    (hK_sum : ∀ x, ∑ y, K x y = 1)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y)
    (hcontract : ∀ f : α → ℝ, piVar π (applyK K f) ≤ (1 - gap) ^ 2 * piVar π f)
    (f : α → ℝ) (t : ℕ) :
    piVar π (applyKIter K t f) ≤ ((1 - gap) ^ 2) ^ t * piVar π f := by
  induction t with
  | zero => simp [applyKIter]
  | succ t ih =>
    have hnn : 0 ≤ (1 - gap) ^ 2 := sq_nonneg _
    have h1 := hcontract (applyKIter K t f)
    have h2 := mul_le_mul_of_nonneg_left ih hnn
    have h3 : (1 - gap) ^ 2 * (((1 - gap) ^ 2) ^ t * piVar π f)
        = ((1 - gap) ^ 2) ^ (t + 1) * piVar π f := by
      rw [pow_succ]; ring
    show piVar π (applyK K (applyKIter K t f)) ≤ _
    calc piVar π (applyK K (applyKIter K t f))
        ≤ (1 - gap) ^ 2 * piVar π (applyKIter K t f) := h1
      _ ≤ (1 - gap) ^ 2 * (((1 - gap) ^ 2) ^ t * piVar π f) := h2
      _ = ((1 - gap) ^ 2) ^ (t + 1) * piVar π f := h3
