/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.BernoulliStreamline

/-!
# Bernoulli along a streamline checks

Concrete consumers of `PhyslibExt.EarthScience.BernoulliStreamline`: the kinetic
identity for the identity flow, and a nonzero uniform flow whose pressure and
potential terms cancel in the Euler balance.

## i. Overview

These are elaboration and non-vacuity checks, not new results. For the identity
flow, the kinetic identity says the directional derivative of `‖x‖^2 / 2` along
`x` is `⟪x, x⟫`. For the uniform flow `u ≡ e₀` (unit speed along the first axis)
with density `ρ = 2`, pressure `p = -2 y₀` and potential `Φ = y₀`, the Euler
balance holds at every point because the convective term vanishes and the
pressure and potential terms cancel: `(1 / 2) * (-2) + 1 = 0`. The Bernoulli head
is then the constant `1 / 2`; both Bernoulli theorems apply, the second along the
straight streamline `γ t = x + t • e₀`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Kinetic identity for the identity flow
- B. Uniform flow: Bernoulli head along the flow and along a streamline
-/

/-- Unit vector along the first coordinate axis. -/
local notation "e₀" => EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The first coordinate `y ↦ y 0`, as a continuous linear functional. -/
local notation "ℓ" => (EuclideanSpace.proj (0 : Fin 3) : StrongDual ℝ (EuclideanSpace ℝ (Fin 3)))

/-! ## A. Kinetic identity for the identity flow -/

/-- Kinetic identity for the identity flow: the directional derivative
of `‖x‖^2 / 2` along `x` is `⟪x, x⟫`. -/
example (x : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2 / 2) x) x =
      @inner ℝ _ _ x x := by
  have hid : HasFDerivAt id (fderiv ℝ id x) x := by
    rw [fderiv_id]
    exact hasFDerivAt_id x
  have h := EarthScience.kinetic_directional_deriv id x hid
  rw [fderiv_id] at h
  simpa using h

/-! ## B. Uniform flow: Bernoulli head along the flow and along a streamline -/

/-- The uniform flow `u ≡ e₀` with `ρ = 2`, `p = -2 y₀`, `Φ = y₀` satisfies the Euler
balance dotted with `u` at every point `x`. -/
lemma uniformFlow_euler (x : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ e₀ ((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => e₀) x) e₀) +
      (1 / 2) * (fderiv ℝ (fun y => -2 * ℓ y) x) e₀ + (fderiv ℝ (fun y => ℓ y) x) e₀ = 0 := by
  rw [fderiv_fun_const, fderiv_const_mul (ContinuousLinearMap.differentiableAt (ℓ)),
    ContinuousLinearMap.fderiv]
  simp only [Pi.zero_apply, zero_apply, inner_zero_right, smul_apply, smul_eq_mul]
  ring

/-- The Bernoulli head of the uniform flow is the constant `‖e₀‖^2 / 2 = 1 / 2`. -/
example (y : EuclideanSpace ℝ (Fin 3)) : -2 * ℓ y / 2 + ‖e₀‖ ^ 2 / 2 + ℓ y = 1 / 2 := by
  rw [PiLp.norm_single]
  norm_num
  ring

/-- Nonzero uniform flow: the Bernoulli head has zero directional derivative along the
flow at every point. -/
example (x : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun y => -2 * ℓ y / 2 + ‖(fun _ : EuclideanSpace ℝ (Fin 3) => e₀) y‖ ^ 2 / 2 +
      ℓ y) x) e₀ = 0 :=
  EarthScience.bernoulli_head_directional_deriv_eq_zero (fun _ => e₀) (fun y => -2 * ℓ y)
    (fun y => ℓ y) 2 (by norm_num) x
    (differentiableAt_const _).hasFDerivAt
    (((ContinuousLinearMap.differentiableAt (ℓ)).const_mul (-2 : ℝ)).hasFDerivAt)
    (ContinuousLinearMap.differentiableAt (ℓ)).hasFDerivAt (uniformFlow_euler x)

/-- Nonzero uniform flow: along the straight streamline `γ t = x + t • e₀`, the
Bernoulli head takes the same value at any two parameters `a`, `b`. -/
example (x : EuclideanSpace ℝ (Fin 3)) (a b : ℝ) :
    -2 * ℓ (x + a • e₀) / 2 + ‖e₀‖ ^ 2 / 2 + ℓ (x + a • e₀) =
      -2 * ℓ (x + b • e₀) / 2 + ‖e₀‖ ^ 2 / 2 + ℓ (x + b • e₀) := by
  have hγ : IsIntegralCurveOn (fun t : ℝ => x + t • e₀) (fun _ _ => e₀) Set.univ := by
    intro t _
    have h := ((hasDerivAt_id t).smul_const e₀).const_add x
    simp only [id_eq, one_smul] at h
    exact h.hasDerivWithinAt
  exact EarthScience.bernoulli_along_streamline (fun _ => e₀) (fun y => -2 * ℓ y)
    (fun y => ℓ y) 2 (by norm_num) (fun t => x + t • e₀) isOpen_univ isPreconnected_univ hγ
    (fun _ _ => differentiableAt_const _)
    (fun _ _ => (ContinuousLinearMap.differentiableAt (ℓ)).const_mul (-2 : ℝ))
    (fun _ _ => ContinuousLinearMap.differentiableAt (ℓ))
    (fun t _ => uniformFlow_euler (x + t • e₀)) (Set.mem_univ a) (Set.mem_univ b)
