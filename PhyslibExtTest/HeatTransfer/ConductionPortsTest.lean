/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.HeatTransfer.ConductionPorts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Quadratic heat-energy identity checks

Concrete consumer of `PhyslibExt.HeatTransfer.ConductionPorts`: the
field `u t x = (t + 2) * x` on `[0, 2]` with `D = 3`, which
satisfies `u_t = D * u_xx + src` with `src t x = x`, `u_x = t + 2`,
`u_xx = 0`. At `t = 1` the energy has derivative `8`: the diffusion
contribution `-3 * 18` and the boundary work `3 * 18` cancel, and
the source power is `∫₀² 3x^2 dx = 8`. The diffusion contribution
at those values is `-54 ≤ 0`, as `diffusion_contribution_nonpos`
asserts for `0 ≤ D`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear field at `t = 1`
- B. Robin seam discharge

## iv. References

None.

## A. Linear field at `t = 1`

-/

/-- Energy identity for `u t x = (t + 2) * x` at `t = 1`, `L = 2`,
`D = 3`: the energy has derivative `8`. -/
example :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2)
      8 1 := by
  have hE : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2)
      (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) * x * x) 1 := by
    have hInt : ∀ τ : ℝ, (∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2) =
        (τ + 2) ^ 2 * (4 / 3) := by
      intro τ
      have h1 : (∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2) =
          (τ + 2) ^ 2 / 2 * ∫ x in (0 : ℝ)..(2 : ℝ), x ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring
      rw [h1, integral_pow]; ring
    have hd : HasDerivAt (fun τ : ℝ => (τ + 2) ^ 2 * (4 / 3))
        ((2 * ((1 : ℝ) + 2)) * (4 / 3)) 1 := by
      have h := ((hasDerivAt_id (1 : ℝ)).add_const (2 : ℝ)).pow 2
      simpa using h.mul_const (4 / 3)
    rw [funext hInt]
    convert hd using 1
    have e1 : (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) * x * x) =
        ((1 : ℝ) + 2) * ∫ x in (0 : ℝ)..(2 : ℝ), x ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [e1, integral_pow]
    norm_num
  have h := ConductionPorts.heatEnergy_hasDerivAt (D := 3) (L := 2)
    (u := fun t x : ℝ => (t + 2) * x) (ut := fun _ x : ℝ => x)
    (ux := fun t _x : ℝ => t + 2) (uxx := fun _ _ : ℝ => 0)
    (src := fun _ x : ℝ => x) (t := 1)
    (by norm_num)
    (fun x _ => by simpa using ((hasDerivAt_id (1 : ℝ)).add_const 2).mul_const x)
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul ((1 : ℝ) + 2))
    (fun x _ => hasDerivAt_const x ((1 : ℝ) + 2))
    (fun _ _ => by ring)
    ((continuous_const.mul continuous_id).continuousOn)
    (continuousOn_const)
    (continuousOn_const)
    hE
    (((continuous_const.mul continuous_id).mul
      continuous_id).intervalIntegrable 0 2)
  convert h using 1
  have e2 : (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) * x * x) =
      ((1 : ℝ) + 2) * ∫ x in (0 : ℝ)..(2 : ℝ), x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [e2, integral_pow]
  norm_num [intervalIntegral.integral_const]

/-- The diffusion contribution at the same values is `-54 ≤ 0`. -/
example :
    -3 * (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) ^ 2) ≤ 0 :=
  ConductionPorts.diffusion_contribution_nonpos (by norm_num) (by norm_num)
    (fun t _x : ℝ => t + 2) 1
    (continuousOn_const.intervalIntegrable)

/-! ## B. Robin seam discharge -/

/-- Seam discharge for the Robin identity: the `hE` hypothesis of
`robinEnergy_hasDerivAt` is exactly the conclusion of
`heatEnergy_hasDerivAt` for `θ = u - Ta` with zero source, given the
PDE-level derivative data for `u`. -/
example {D L k h0 hL Ta t : ℝ} (hk : 0 < k) (hL0 : 0 ≤ L)
    {u ut ux uxx : ℝ → ℝ → ℝ}
    (hut : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hux : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y : ℝ => u t y) (ux t x) x)
    (huxx : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y : ℝ => ux t y) (uxx t x) x)
    (hPDE : ∀ x ∈ Set.uIcc 0 L, ut t x = D * uxx t x)
    (hcont_u : ContinuousOn (fun x : ℝ => u t x) (Set.Icc 0 L))
    (hcont_ux : ContinuousOn (fun x : ℝ => ux t x) (Set.Icc 0 L))
    (hcont_uxx : ContinuousOn (fun x : ℝ => uxx t x) (Set.Icc 0 L))
    (hEθ : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u τ x - Ta) ^ 2 / 2)
      (∫ x in (0 : ℝ)..L, (u t x - Ta) * ut t x) t)
    (hint : IntervalIntegrable (fun x : ℝ => (u t x - Ta) * ut t x)
      MeasureTheory.volume 0 L)
    (hBC0 : k * ux t 0 = h0 * (u t 0 - Ta))
    (hBCL : -k * ux t L = hL * (u t L - Ta)) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u τ x - Ta) ^ 2 / 2)
      (-D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) -
        D / k * (h0 * (u t 0 - Ta) ^ 2 + hL * (u t L - Ta) ^ 2)) t :=
  ConductionPorts.robinEnergy_hasDerivAt hk hBC0 hBCL
    (ConductionPorts.heatEnergy_hasDerivAt
      (u := fun τ x : ℝ => u τ x - Ta) (ut := ut) (ux := ux) (uxx := uxx)
      (src := fun _ _ : ℝ => 0) hL0
      (fun x hx => (hut x hx).sub_const Ta)
      (fun x hx => (hux x hx).sub_const Ta)
      huxx
      (fun x hx => by simp [hPDE x hx])
      (hcont_u.sub continuousOn_const) hcont_ux hcont_uxx hEθ hint)

/-- Seam discharge for uniqueness: the `hEw` hypothesis of
`robin_uniqueness` is the conclusion of `heatEnergy_hasDerivAt` for
the difference field, given source-free PDE data for both fields. -/
example {D L k h0 hL Ta T : ℝ} (hD : 0 ≤ D) (hL0 : 0 < L)
    (hk : 0 < k) (hh0 : 0 ≤ h0) (hhL : 0 ≤ hL)
    {u1 u2 ut1 ut2 ux1 ux2 uxx1 uxx2 : ℝ → ℝ → ℝ}
    (hut1 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L,
      HasDerivAt (fun τ : ℝ => u1 τ x) (ut1 t x) t)
    (hut2 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L,
      HasDerivAt (fun τ : ℝ => u2 τ x) (ut2 t x) t)
    (hux1 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L,
      HasDerivAt (fun y : ℝ => u1 t y) (ux1 t x) x)
    (hux2 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L,
      HasDerivAt (fun y : ℝ => u2 t y) (ux2 t x) x)
    (huxx1 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L,
      HasDerivAt (fun y : ℝ => ux1 t y) (uxx1 t x) x)
    (huxx2 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L,
      HasDerivAt (fun y : ℝ => ux2 t y) (uxx2 t x) x)
    (hPDE1 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L, ut1 t x = D * uxx1 t x)
    (hPDE2 : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.uIcc 0 L, ut2 t x = D * uxx2 t x)
    (hcont_w : ∀ t ∈ Set.Ioo 0 T,
      ContinuousOn (fun x : ℝ => u1 t x - u2 t x) (Set.Icc 0 L))
    (hcont_wx : ∀ t ∈ Set.Ioo 0 T,
      ContinuousOn (fun x : ℝ => ux1 t x - ux2 t x) (Set.Icc 0 L))
    (hcont_wxx : ∀ t ∈ Set.Ioo 0 T,
      ContinuousOn (fun x : ℝ => uxx1 t x - uxx2 t x) (Set.Icc 0 L))
    (hEw0 : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2)
        (∫ x in (0 : ℝ)..L, (u1 t x - u2 t x) * (ut1 t x - ut2 t x)) t)
    (hintw : ∀ t ∈ Set.Ioo 0 T,
      IntervalIntegrable (fun x : ℝ => (u1 t x - u2 t x) * (ut1 t x - ut2 t x))
        MeasureTheory.volume 0 L)
    (hBC0₁ : ∀ t ∈ Set.Ioo 0 T, k * ux1 t 0 = h0 * (u1 t 0 - Ta))
    (hBCL₁ : ∀ t ∈ Set.Ioo 0 T, -k * ux1 t L = hL * (u1 t L - Ta))
    (hBC0₂ : ∀ t ∈ Set.Ioo 0 T, k * ux2 t 0 = h0 * (u2 t 0 - Ta))
    (hBCL₂ : ∀ t ∈ Set.Ioo 0 T, -k * ux2 t L = hL * (u2 t L - Ta))
    (hEcont : ContinuousOn
      (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) (Set.Icc 0 T))
    (hwcont : ∀ t ∈ Set.Icc 0 T,
      ContinuousOn (fun x : ℝ => u1 t x - u2 t x) (Set.Icc 0 L))
    (hinit : ∀ x ∈ Set.Icc 0 L, u1 0 x = u2 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x ∈ Set.Icc 0 L, u1 t x = u2 t x :=
  ConductionPorts.robin_uniqueness hD hL0 hk hh0 hhL hBC0₁ hBCL₁ hBC0₂ hBCL₂
    (fun t ht => ConductionPorts.heatEnergy_hasDerivAt
      (u := fun τ x : ℝ => u1 τ x - u2 τ x)
      (ut := fun τ x : ℝ => ut1 τ x - ut2 τ x)
      (ux := fun τ x : ℝ => ux1 τ x - ux2 τ x)
      (uxx := fun τ x : ℝ => uxx1 τ x - uxx2 τ x)
      (src := fun _ _ : ℝ => 0) hL0.le
      (fun x hx => (hut1 t ht x hx).sub (hut2 t ht x hx))
      (fun x hx => (hux1 t ht x hx).sub (hux2 t ht x hx))
      (fun x hx => (huxx1 t ht x hx).sub (huxx2 t ht x hx))
      (fun x hx => by rw [hPDE1 t ht x hx, hPDE2 t ht x hx]; ring)
      (hcont_w t ht) (hcont_wx t ht) (hcont_wxx t ht) (hEw0 t ht) (hintw t ht))
    hEcont hwcont hinit
