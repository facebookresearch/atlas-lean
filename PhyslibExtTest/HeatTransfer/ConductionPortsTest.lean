/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.HeatTransfer.ConductionPorts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
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
- C. Fin fixtures
- D. Thermal network fixtures

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

/-! ## C. Fin fixtures -/

section FinFixtures

open Real Set Filter Topology ConductionPorts MathlibExt.Biology.Biophysics.MembraneCable

/-- Nonzero fixture: `k = A = h = P = L = 1` (so `m = 1`), `Ta = 300`, base excess `50`. The
transfer solution with `q 0 = 50 * tanh 1` is a fin steady state with an adiabatic tip and a
positive base heat rate. -/
example :
    IsFinSteadyState 1 1 1 1 300 1 (fun x => 300 + cableVoltage 1 1 50 (50 * Real.tanh 1) x)
        (cableCurrent 1 1 50 (50 * Real.tanh 1)) ∧
      cableCurrent 1 1 50 (50 * Real.tanh 1) 1 = 0 ∧
      (300 + cableVoltage 1 1 50 (50 * Real.tanh 1) 0) - 300 = 50 ∧
      0 < cableCurrent 1 1 50 (50 * Real.tanh 1) 0 := by
  have e1 : (1:ℝ) / (1 * 1) = 1 := by norm_num
  have hbase := isSteadyState_cable (show (0:ℝ) < 1 from zero_lt_one)
    (show (0:ℝ) < 1 from zero_lt_one) (Icc (0:ℝ) 1) 50 (50 * Real.tanh 1)
  have hfun : (fun x : ℝ => (300 + cableVoltage 1 1 50 (50 * Real.tanh 1) x) - 300) =
      cableVoltage 1 1 50 (50 * Real.tanh 1) := by
    funext x
    ring
  have hfin : IsFinSteadyState 1 1 1 1 300 1
      (fun x => 300 + cableVoltage 1 1 50 (50 * Real.tanh 1) x)
      (cableCurrent 1 1 50 (50 * Real.tanh 1)) := by
    rw [isFinSteadyState_iff, e1, hfun]
    exact hbase
  have hlam1 : lengthConstant (1:ℝ) 1 = 1 := by
    unfold lengthConstant
    rw [div_one, Real.sqrt_one]
  have hr1 : charResistance (1:ℝ) 1 = 1 := by
    unfold charResistance
    rw [mul_one, Real.sqrt_one]
  have hc : Real.cosh (1:ℝ) ≠ 0 := (cosh_pos _).ne'
  have htc : Real.sinh 1 / Real.cosh 1 * Real.cosh 1 = Real.sinh 1 :=
    div_mul_cancel₀ _ hc
  have hcc : cableCurrent 1 1 50 (50 * Real.tanh 1) 1 = 0 := by
    simp only [cableCurrent, hlam1, hr1, div_one, Real.tanh_eq_sinh_div_cosh]
    linear_combination 50 * htc
  have hcv0 : cableVoltage 1 1 50 (50 * Real.tanh 1) 0 = 50 := by
    simp only [cableVoltage, hlam1, hr1, div_one, Real.cosh_zero, Real.sinh_zero,
      mul_one, mul_zero, sub_zero]
  have ht1 : (0:ℝ) < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (sinh_pos_iff.2 zero_lt_one) (cosh_pos _)
  have hcc0 : cableCurrent 1 1 50 (50 * Real.tanh 1) 0 = 50 * Real.tanh 1 := by
    simp only [cableCurrent, hlam1, hr1, div_one, Real.cosh_zero, Real.sinh_zero,
      mul_one, mul_zero, sub_zero]
  refine ⟨hfin, hcc, ?_, ?_⟩
  · rw [hcv0]
    norm_num
  · rw [hcc0]
    exact mul_pos (show (0:ℝ) < 50 by norm_num) ht1

/-- Small `m L` is a limit: `tanh x / x → 1` as `x → 0⁺`, while the expression evaluated at
`x = 0` is `0` (division by zero), not the limit. -/
example :
    Tendsto (fun x : ℝ => Real.tanh x / x) (𝓝[>] 0) (𝓝 1) ∧ Real.tanh 0 / 0 = 0 := by
  have hsinh : Tendsto (fun x' : ℝ => Real.sinh x' / x') (𝓝[≠] 0) (𝓝 1) := by
    have h := (Real.hasDerivAt_sinh 0).tendsto_slope
    rw [slope_fun_def_field, Real.sinh_zero, Real.cosh_zero] at h
    simpa only [sub_zero] using h
  have hcosh : Tendsto (fun x' : ℝ => Real.cosh x') (𝓝[≠] 0) (𝓝 1) := by
    have h : Tendsto (fun x' : ℝ => Real.cosh x') (𝓝 (0:ℝ)) (𝓝 (Real.cosh 0)) :=
      Real.continuous_cosh.tendsto 0
    have h2 := h.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    rwa [Real.cosh_zero] at h2
  have hdiv := hsinh.div hcosh (by norm_num : (1:ℝ) ≠ 0)
  rw [div_one] at hdiv
  have hfun : (fun x' : ℝ => Real.tanh x' / x') =
      fun x' => (Real.sinh x' / x') / Real.cosh x' := by
    funext x'
    rw [Real.tanh_eq_sinh_div_cosh, div_right_comm]
  rw [hfun]
  refine ⟨?_, div_zero _⟩
  exact hdiv.mono_left (nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx))

end FinFixtures

/-! ## D. Thermal network fixtures -/

section ThermalNetworkFixtures

open ConductionPorts

/-- Derivatives and network equations of the two-node solution, shared by the checks below. -/
private lemma twoNode_trajectory :
    let C : Fin 2 → ℝ := ![1, 2]
    let G : Fin 2 → Fin 2 → ℝ := ![![0, 2], ![2, 0]]
    let T : Fin 2 → ℝ → ℝ :=
      ![fun t => 1000 / 3 + 200 / 3 * Real.exp (-3 * t),
        fun t => 1000 / 3 - 100 / 3 * Real.exp (-3 * t)]
    let dT : Fin 2 → ℝ → ℝ :=
      ![fun t => -200 * Real.exp (-3 * t), fun t => 100 * Real.exp (-3 * t)]
    (∀ i t, HasDerivAt (T i) (dT i t) t) ∧
      ∀ i t, C i * dT i t = ∑ j, G i j * (T j t - T i t) := by
  refine ⟨?_, ?_⟩
  · intro i t
    fin_cases i
    · simp only [Fin.mk_zero, Matrix.cons_val_zero]
      have hinner : HasDerivAt (fun t : ℝ => -3 * t) (-3 * 1) t := by
        simpa using (hasDerivAt_id t).const_mul (-3)
      have hexp := hinner.exp
      have hmul := hexp.const_mul (200 / 3)
      have hadd := hmul.const_add (1000 / 3)
      convert hadd using 1
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hinner : HasDerivAt (fun t : ℝ => -3 * t) (-3 * 1) t := by
        simpa using (hasDerivAt_id t).const_mul (-3)
      have hexp := hinner.exp
      have hmul := hexp.const_mul (100 / 3)
      have hsub := (hasDerivAt_const t (1000 / 3)).sub hmul
      convert hsub using 1
      ring
  · intro i t
    fin_cases i
    · simp only [Fin.sum_univ_two, Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · simp only [Fin.sum_univ_two, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring

/-- Two-node fixture: `C = (1, 2)`, `G 0 1 = G 1 0 = 2`, no self-conductance, no inputs, initial
temperatures `400` and `300`. The pair `T 0 t = 1000/3 + (200/3) e^{-3t}`,
`T 1 t = 1000/3 - (100/3) e^{-3t}` solves the network equations for every `t`, keeps the stored
heat at `1000`, and has quadratic-functional rate `-20000` at `t = 0`. -/
example :
    let C : Fin 2 → ℝ := ![1, 2]
    let G : Fin 2 → Fin 2 → ℝ := ![![0, 2], ![2, 0]]
    let T : Fin 2 → ℝ → ℝ :=
      ![fun t => 1000 / 3 + 200 / 3 * Real.exp (-3 * t),
        fun t => 1000 / 3 - 100 / 3 * Real.exp (-3 * t)]
    let dT : Fin 2 → ℝ → ℝ :=
      ![fun t => -200 * Real.exp (-3 * t), fun t => 100 * Real.exp (-3 * t)]
    (∀ i, 0 < C i) ∧ (∀ i j, 0 ≤ G i j) ∧ (∀ i j, G i j = G j i) ∧
      (∀ i t, HasDerivAt (T i) (dT i t) t) ∧
      (∀ i t, C i * dT i t = ∑ j, G i j * (T j t - T i t)) ∧
      T 0 0 = 400 ∧ T 1 0 = 300 ∧
      (∀ t, ∑ i, C i * T i t = 1000) ∧
      -∑ i, ∑ j, G i j * (T i 0 - T j 0) ^ 2 / 2 = -20000 := by
  obtain ⟨hT, hbal⟩ := twoNode_trajectory
  have e0 : Real.exp (-3 * (0 : ℝ)) = 1 := by rw [mul_zero, Real.exp_zero]
  refine ⟨?_, ?_, ?_, hT, hbal, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · simp only [Matrix.cons_val_zero, e0]
    norm_num
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e0]
    norm_num
  · intro t
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e0]
    norm_num

/-- Consumers on the two-node solution: the storage balance gives stored-heat derivative `0` at
every time, and the quadratic identity gives the derivative `-20000` at `t = 0`. -/
example :
    let C : Fin 2 → ℝ := ![1, 2]
    let T : Fin 2 → ℝ → ℝ :=
      ![fun t => 1000 / 3 + 200 / 3 * Real.exp (-3 * t),
        fun t => 1000 / 3 - 100 / 3 * Real.exp (-3 * t)]
    (∀ t, HasDerivAt (fun τ => ∑ i, C i * T i τ) 0 t) ∧
      HasDerivAt (fun τ => ∑ i, C i * T i τ ^ 2 / 2) (-20000) 0 := by
  obtain ⟨hT, hbal⟩ := twoNode_trajectory
  have hG : ∀ i j, (![![0, 2], ![2, 0]] : Fin 2 → Fin 2 → ℝ) i j =
      (![![0, 2], ![2, 0]] : Fin 2 → Fin 2 → ℝ) j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have e0 : Real.exp (-3 * (0 : ℝ)) = 1 := by rw [mul_zero, Real.exp_zero]
  refine ⟨fun t => ?_, ?_⟩
  · have h := hasDerivAt_thermalStorage (Q := fun _ => 0) hG (fun i => hT i t)
      (fun i => (hbal i t).trans (add_zero _).symm)
    simp only [Finset.sum_const_zero] at h
    exact h
  · have h := hasDerivAt_quadraticFunctional hG (fun i => hT i 0) (fun i => hbal i 0)
    convert h using 1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e0]
    norm_num

/-- Consumers of the sign lemmas at `T = (400, 300)`: the quadratic functional is nonnegative
for `C = (1, 2)` and its rate is nonpositive for the nonnegative conductances. -/
example :
    0 ≤ ∑ i, (![1, 2] : Fin 2 → ℝ) i * (![400, 300] : Fin 2 → ℝ) i ^ 2 / 2 ∧
      -∑ i, ∑ j, (![![0, 2], ![2, 0]] : Fin 2 → Fin 2 → ℝ) i j *
        ((![400, 300] : Fin 2 → ℝ) i - (![400, 300] : Fin 2 → ℝ) j) ^ 2 / 2 ≤ 0 :=
  ⟨quadraticFunctional_nonneg (fun i => by fin_cases i <;> norm_num) _,
    quadraticFunctional_rate_nonpos (fun i j => by fin_cases i <;> fin_cases j <;> norm_num) _⟩

/-- Invalid: a negative conductance `G 0 1 = G 1 0 = -1` violates the sign hypothesis of
`quadraticFunctional_rate_nonpos` and makes the quadratic functional grow: at `T = (1, 0)` the
rate is `1 > 0`. -/
example :
    let G : Fin 2 → Fin 2 → ℝ := ![![0, -1], ![-1, 0]]
    let T : Fin 2 → ℝ := ![1, 0]
    ¬ (∀ i j, 0 ≤ G i j) ∧ 0 < -∑ i, ∑ j, G i j * (T i - T j) ^ 2 / 2 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h01 := h 0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h01
    norm_num at h01
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-- The same negative conductance through the derivative identity, which needs only symmetry:
with `C = (1, 1)`, the motion `T 0 s = 1 + s`, `T 1 s = -s` obeys the network equations at
`s = 0`, and the quadratic functional has derivative `1 > 0` there. -/
example :
    HasDerivAt (fun τ => ∑ i, (![1, 1] : Fin 2 → ℝ) i *
        (![fun s => 1 + s, fun s => -s] : Fin 2 → ℝ → ℝ) i τ ^ 2 / 2) 1 0 := by
  have hG : ∀ i j, (![![0, -1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) i j =
      (![![0, -1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hT : ∀ i, HasDerivAt ((![fun s => 1 + s, fun s => -s] : Fin 2 → ℝ → ℝ) i)
      ((![1, -1] : Fin 2 → ℝ) i) 0 := by
    intro i
    fin_cases i
    · simpa using (hasDerivAt_id' (0 : ℝ)).const_add 1
    · simpa using hasDerivAt_neg (0 : ℝ)
  have h := hasDerivAt_quadraticFunctional (C := ![1, 1]) hG hT (fun i => by
    fin_cases i <;> norm_num [Fin.sum_univ_two])
  convert h using 1
  norm_num [Fin.sum_univ_two]

/-- Invalid: a negative capacity `C = (1, -2)` violates the sign hypothesis of
`quadraticFunctional_nonneg` and makes the quadratic functional indefinite: at `T = (0, 1)` it
is `-1 < 0`. -/
example :
    let C : Fin 2 → ℝ := ![1, -2]
    let T : Fin 2 → ℝ := ![0, 1]
    ¬ (∀ i, 0 ≤ C i) ∧ ∑ i, C i * T i ^ 2 / 2 < 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    norm_num at h1
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

end ThermalNetworkFixtures
