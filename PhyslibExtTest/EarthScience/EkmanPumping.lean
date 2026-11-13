/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.EkmanPumping
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ekman pumping checks

Concrete consumers of `PhyslibExt.EarthScience.EkmanPumping`, stated
with the canonical transport `EarthScience.ekmanTransport`: the stress
field `τ (x, y) = (x * y, x ^ 2 - y, 0)` at `(x, y) = (1, 2)` with
`ρ₀ = 1`, where the curl is `1` and the transport divergence is `1 / 2`
for `f = 2`; the upwelling sign for `f = 2` and the downwelling sign for
`f = -2`; the general hemispheric sign statements; and the Ekman balance
of `EarthScience.ekman_transport` holding for the same transport whose
divergence is computed.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
partial derivatives of the concrete stress field are `∂ₓ (τ 1) = 2 * x`
and `∂ᵧ (τ 0) = x`, so at `(1, 2)` the curl is `2 - 1 = 1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete stress field
- B. Hemispheric signs and the Ekman balance

## iv. References

- `PhyslibExt.EarthScience.EkmanPumping`
- `PhyslibExt.EarthScience.EkmanLayers`
-/

open Matrix

/-! ## A. Concrete stress field -/

/-- Divergence of the transport `ekmanTransport 1 2 (τ x y)` for the
concrete stress field at `(1, 2)`, computed with
`ekman_pumping_divergence`: the curl is `1` and `ρ₀ f = 2`, so the
divergence is `1 / 2`. -/
example :
    deriv (fun x' : ℝ => EarthScience.ekmanTransport 1 2 ![x' * 2, x' ^ 2 - 2, 0] 0) 1 +
      deriv (fun y' : ℝ => EarthScience.ekmanTransport 1 2 ![1 * y', 1 ^ 2 - y', 0] 1) 2 =
    1 / 2 := by
  have hx : HasDerivAt (fun x' : ℝ => (![x' * 2, x' ^ 2 - 2, 0] : Fin 3 → ℝ) 1) 2 1 := by
    simpa using ((hasDerivAt_id' (x := (1 : ℝ))).pow 2).sub_const (2 : ℝ)
  have hy : HasDerivAt (fun y' : ℝ => (![1 * y', 1 ^ 2 - y', 0] : Fin 3 → ℝ) 0) 1 2 := by
    simpa using (hasDerivAt_id' (x := (2 : ℝ))).const_mul (1 : ℝ)
  rw [EarthScience.ekman_pumping_divergence (fun x y => ![x * y, x ^ 2 - y, 0]) 1 2 1 2
    (by norm_num) hx.differentiableAt.hasDerivAt hy.differentiableAt.hasDerivAt,
    hx.deriv, hy.deriv]
  norm_num

/-! ## B. Hemispheric signs and the Ekman balance -/

/-- Northern hemisphere, concrete: for the same stress field with `ρ₀ = 1`
and `f = 2 > 0`, the positive curl gives a positive divergence of
`ekmanTransport 1 2 (τ x y)` (upwelling) by `ekman_pumping_sign`. -/
example :
    0 < deriv (fun x' : ℝ => EarthScience.ekmanTransport 1 2 ![x' * 2, x' ^ 2 - 2, 0] 0) 1 +
      deriv (fun y' : ℝ => EarthScience.ekmanTransport 1 2 ![1 * y', 1 ^ 2 - y', 0] 1) 2 := by
  have hx : HasDerivAt (fun x' : ℝ => (![x' * 2, x' ^ 2 - 2, 0] : Fin 3 → ℝ) 1) 2 1 := by
    simpa using ((hasDerivAt_id' (x := (1 : ℝ))).pow 2).sub_const (2 : ℝ)
  have hy : HasDerivAt (fun y' : ℝ => (![1 * y', 1 ^ 2 - y', 0] : Fin 3 → ℝ) 0) 1 2 := by
    simpa using (hasDerivAt_id' (x := (2 : ℝ))).const_mul (1 : ℝ)
  refine (EarthScience.ekman_pumping_sign (fun x y => ![x * y, x ^ 2 - y, 0]) 1 2 1 2
    one_pos hx.differentiableAt.hasDerivAt hy.differentiableAt.hasDerivAt ?_).1 (by norm_num)
  rw [hx.deriv, hy.deriv]
  norm_num

/-- Southern hemisphere, concrete: for the same stress field with `ρ₀ = 1`
and `f = -2 < 0`, the positive curl gives a negative divergence of
`ekmanTransport 1 (-2) (τ x y)` (downwelling) by `ekman_pumping_sign`. -/
example :
    deriv (fun x' : ℝ => EarthScience.ekmanTransport 1 (-2) ![x' * 2, x' ^ 2 - 2, 0] 0) 1 +
      deriv (fun y' : ℝ => EarthScience.ekmanTransport 1 (-2) ![1 * y', 1 ^ 2 - y', 0] 1) 2
      < 0 := by
  have hx : HasDerivAt (fun x' : ℝ => (![x' * 2, x' ^ 2 - 2, 0] : Fin 3 → ℝ) 1) 2 1 := by
    simpa using ((hasDerivAt_id' (x := (1 : ℝ))).pow 2).sub_const (2 : ℝ)
  have hy : HasDerivAt (fun y' : ℝ => (![1 * y', 1 ^ 2 - y', 0] : Fin 3 → ℝ) 0) 1 2 := by
    simpa using (hasDerivAt_id' (x := (2 : ℝ))).const_mul (1 : ℝ)
  refine (EarthScience.ekman_pumping_sign (fun x y => ![x * y, x ^ 2 - y, 0]) 1 (-2) 1 2
    one_pos hx.differentiableAt.hasDerivAt hy.differentiableAt.hasDerivAt ?_).2 (by norm_num)
  rw [hx.deriv, hy.deriv]
  norm_num

/-- Northern hemisphere, general: with positive stress curl, the divergence
of the Ekman transport is positive (upwelling). -/
example (τ : ℝ → ℝ → Fin 3 → ℝ) (ρ₀ f x y : ℝ) (hρ : 0 < ρ₀) (hf : 0 < f)
    (hτ₁x : HasDerivAt (fun x' => τ x' y 1) (deriv (fun x' => τ x' y 1) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ x y' 0) (deriv (fun y' => τ x y' 0) y) y)
    (hcurl : 0 < deriv (fun x' => τ x' y 1) x - deriv (fun y' => τ x y' 0) y) :
    0 < deriv (fun x' => EarthScience.ekmanTransport ρ₀ f (τ x' y) 0) x +
      deriv (fun y' => EarthScience.ekmanTransport ρ₀ f (τ x y') 1) y :=
  (EarthScience.ekman_pumping_sign τ ρ₀ f x y hρ hτ₁x hτ₀y hcurl).1 hf

/-- Southern hemisphere, general: with positive stress curl, the divergence
of the Ekman transport is negative (downwelling). -/
example (τ : ℝ → ℝ → Fin 3 → ℝ) (ρ₀ f x y : ℝ) (hρ : 0 < ρ₀) (hf : f < 0)
    (hτ₁x : HasDerivAt (fun x' => τ x' y 1) (deriv (fun x' => τ x' y 1) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ x y' 0) (deriv (fun y' => τ x y' 0) y) y)
    (hcurl : 0 < deriv (fun x' => τ x' y 1) x - deriv (fun y' => τ x y' 0) y) :
    deriv (fun x' => EarthScience.ekmanTransport ρ₀ f (τ x' y) 0) x +
      deriv (fun y' => EarthScience.ekmanTransport ρ₀ f (τ x y') 1) y < 0 :=
  (EarthScience.ekman_pumping_sign τ ρ₀ f x y hρ hτ₁x hτ₀y hcurl).2 hf

/-- The transport whose divergence `ekman_pumping_divergence` computes is the
one that satisfies the Ekman balance `ekman_transport` at `(x, y)`. -/
example (τ : ℝ → ℝ → Fin 3 → ℝ) (ρ₀ f x y : ℝ) (hρ : 0 < ρ₀) (hf : f ≠ 0)
    (hτ : τ x y 2 = 0)
    (hτ₁x : HasDerivAt (fun x' => τ x' y 1) (deriv (fun x' => τ x' y 1) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ x y' 0) (deriv (fun y' => τ x y' 0) y) y) :
    (ρ₀ * f) • ((![0, 0, 1] : Fin 3 → ℝ) ⨯₃ EarthScience.ekmanTransport ρ₀ f (τ x y)) =
        τ x y ∧
      deriv (fun x' => EarthScience.ekmanTransport ρ₀ f (τ x' y) 0) x +
          deriv (fun y' => EarthScience.ekmanTransport ρ₀ f (τ x y') 1) y =
        (deriv (fun x' => τ x' y 1) x - deriv (fun y' => τ x y' 0) y) / (ρ₀ * f) :=
  ⟨EarthScience.ekman_transport ρ₀ f hρ hf (τ x y) hτ,
    EarthScience.ekman_pumping_divergence τ ρ₀ f x y (mul_ne_zero hρ.ne' hf) hτ₁x hτ₀y⟩
