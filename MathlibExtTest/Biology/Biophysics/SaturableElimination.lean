/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.SaturableElimination

/-! Tests for saturable (Michaelis–Menten) elimination: concrete steady states and AUC values,
non-vacuity witnesses for `IsSolution`, the dose–AUC nonlinearity, and the boundary regimes
`R = Vmax` (no steady state) and `R > Vmax` (unbounded accumulation). -/

open Real Set Filter Topology MeasureTheory

namespace MathlibExtTest.Biology.Biophysics.SaturableElimination

open MathlibExt.Biology.Biophysics.SaturableElimination
open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate)
open MathlibExt.Biology.Biophysics.CompartmentKinetics (amount concentration amount_bolus)

/-- `Vmax = 2`, `Km = 1`, `R = 1`: `C∞ = 1 · 1 / (2 - 1) = 1`. -/
example : steadyConc 2 1 1 = 1 := by norm_num [steadyConc]

/-- At the steady state elimination balances infusion: `mmRate 2 1 1 = 2 · 1 / 2 = 1`. -/
example : mmRate 2 1 (steadyConc 2 1 1) = 1 :=
  mmRate_steadyConc (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuity: the steady state is a (constant) solution. -/
example : IsSolution 2 1 1 (fun _ ↦ 1) := by
  have := isSolution_steadyConc (Vmax := 2) (Km := 1) (R := 1) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num [steadyConc] at this
  exact this

/-- No dose, no infusion: `C ≡ 0` is a solution. -/
example : IsSolution 2 1 0 (fun _ ↦ 0) := isSolution_const_iff.2 (by simp [mmRate])

/-- A nonzero constant is not a bolus solution (`Vmax > 0`, `R = 0`). -/
example : ¬ IsSolution 2 1 0 (fun _ ↦ 3) := by
  rw [isSolution_const_iff]; norm_num [mmRate]

/-- Existence for a bolus `C₀ = 4` (`Vmax = 2`, `Km = 1`). -/
example : ∃ C : ℝ → ℝ, IsSolution 2 1 0 C ∧ C 0 = 4 ∧ ∀ t, 0 ≤ t → 0 ≤ C t :=
  exists_isSolution (by norm_num) (by norm_num) le_rfl (by norm_num)

/-- Uniqueness: a solution starting at the steady state stays there. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 1 C) (h0 : C 0 = 1) (t : ℝ) (ht : 0 ≤ t) : C t = 1 := by
  have hs : IsSolution 2 1 1 (fun _ ↦ (1 : ℝ)) := isSolution_const_iff.2 (by norm_num [mmRate])
  exact h.eq_of_eq hs (by norm_num) (by norm_num) (by norm_num) (by rw [h0]; norm_num) h0 ht

/-- Bolus bracket at `C₀ = 4`, `Vmax = 2`, `Km = 1`: between washouts at rates `2` and `2/5`. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 0 C) (h0 : C 0 = 4) (t : ℝ) (ht : 0 ≤ t) :
    4 * exp (-(2 * t)) ≤ C t ∧ C t ≤ 4 * exp (-(2 / 5 * t)) := by
  have h1 := h.amount_le (by norm_num) (by norm_num) le_rfl (by rw [h0]; norm_num) ht
  have h2 := h.le_amount_bolus (by norm_num) (by norm_num) (by rw [h0]; norm_num) ht
  rw [amount_bolus, h0] at h1 h2
  norm_num at h1 h2
  exact ⟨h1, h2⟩

/-- Strict positivity for a positive bolus. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 0 C) (h0 : C 0 = 4) : 0 < C 10 :=
  h.pos (by norm_num) (by norm_num) le_rfl (by rw [h0]; norm_num) (by norm_num)

/-- Zero-order bounds with infusion `R = 1`, `Vmax = 2`: `4 - t ≤ C(t) ≤ 4 + t`. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 1 C) (h0 : C 0 = 4) (t : ℝ) (ht : 0 ≤ t) :
    4 - t ≤ C t ∧ C t ≤ 4 + t := by
  have h1 := h.add_mul_le (by norm_num) (by norm_num) (by norm_num) (by rw [h0]; norm_num) ht
  have h2 := h.le_add_mul (by norm_num) (by norm_num) (by norm_num) (by rw [h0]; norm_num) ht
  rw [h0] at h1 h2
  constructor <;> linarith

/-- Mass balance at `t = 3` for a bolus `C₀ = 4`. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 0 C) (h0 : C 0 = 4) :
    C 3 + ∫ s in (0)..3, mmRate 2 1 (C s) = 4 := by
  have := h.add_integral_eq (by norm_num) (by norm_num) le_rfl (by rw [h0]; norm_num)
    (t := 3) (by norm_num)
  rw [h0] at this
  linarith

/-- `Vmax = 2`, `Km = 1`, `C₀ = 2`: `AUC = 2 (1 + 1) / 2 = 2`. -/
example : bolusAUC 2 1 2 = 2 := by norm_num [bolusAUC]

/-- The AUC of the bolus solution with `C₀ = 2` is `2`. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 0 C) (h0 : C 0 = 2) : ∫ t in Ioi 0, C t = 2 := by
  rw [h.integral_Ioi_bolus (by norm_num) (by norm_num) (by rw [h0]; norm_num), h0]
  norm_num [bolusAUC]

/-- Finite-horizon AUC via the integrated balance. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 0 C) (h0 : C 0 = 2) :
    ∫ t in (0)..5, C t = (1 * (2 - C 5) + (2 ^ 2 - C 5 ^ 2) / 2) / 2 := by
  rw [h.integral_bolus (by norm_num) (by norm_num) (by rw [h0]; norm_num) (by norm_num), h0]

/-- Dose nonlinearity: `AUC(2) = 2 < AUC(4) = 4 (1 + 2) / 2 = 6`, more than twice `AUC(2)`. -/
example : bolusAUC 2 1 4 = 6 := by norm_num [bolusAUC]

example : 2 * bolusAUC 2 1 2 < bolusAUC 2 1 (2 * 2) := two_mul_bolusAUC_lt (by norm_num) two_pos

example : ¬ ∃ a, ∀ C₀, 0 ≤ C₀ → bolusAUC 2 1 C₀ = a * C₀ := not_exists_bolusAUC_eq_mul two_pos

/-- Linear split at `Vmax = 2`, `Km = 1`, `V = 10`, `C₀ = 2`: linear part `C₀ Km / Vmax = 1`,
saturation part `C₀² / (2 Vmax) = 1`. -/
example : (∫ t in Ici 0, concentration (10 * 2 / 1) 10 0 (10 * 2) t) = 1 := by
  have := bolusAUC_eq_integral_linear_add (Vmax := 2) (Km := 1) (V := 10) (by norm_num)
    (by norm_num) (by norm_num) 2
  norm_num [bolusAUC] at this
  linarith

/-- Low-dose limit of the dose-normalized AUC: `Km / Vmax = 1 / 2`. -/
example : Tendsto (fun C₀ ↦ bolusAUC 2 1 C₀ / C₀) (𝓝[>] 0) (𝓝 (1 / 2)) :=
  tendsto_bolusAUC_div 2 1

/-- Infusion `R = 1 < Vmax = 2` from an empty compartment: convergence to `C∞ = 1`. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 1 C) (h0 : C 0 = 0) : Tendsto C atTop (𝓝 1) := by
  have := h.tendsto_steadyConc (by norm_num) (by norm_num) (by norm_num) (by rw [h0])
  norm_num [steadyConc] at this
  exact this

/-- Explicit rate from an empty compartment: `|C(t) - 1| ≤ e^{-t/3}` (`λ = 1 / (1 + 1 + 1)`). -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 1 C) (h0 : C 0 = 0) (t : ℝ) (ht : 0 ≤ t) :
    |C t - 1| ≤ exp (-(1 / 3 * t)) := by
  have := h.abs_sub_steadyConc_le (by norm_num) (by norm_num) (by norm_num) (by rw [h0]) ht
  rw [h0] at this
  norm_num [steadyConc] at this
  exact this

/-- Boundary `R = Vmax = 2`: no nonnegative steady state. -/
example (c : ℝ) (hc : 0 ≤ c) : ¬ IsSolution 2 1 2 (fun _ ↦ c) :=
  not_isSolution_const_of_le (by norm_num) (by norm_num) le_rfl hc

/-- Boundary `R = 3 > Vmax = 2`: unbounded accumulation. -/
example {C : ℝ → ℝ} (h : IsSolution 2 1 3 C) (h0 : C 0 = 0) : Tendsto C atTop atTop :=
  h.tendsto_atTop (by norm_num) (by norm_num) (by norm_num) (by rw [h0])

/-- Dose-normalized AUC increases with dose. -/
example : bolusAUC 2 1 1 / 1 < bolusAUC 2 1 2 / 2 :=
  strictMonoOn_bolusAUC_div two_pos (by norm_num : (1 : ℝ) ∈ Ioi 0)
    (by norm_num : (2 : ℝ) ∈ Ioi 0) (by norm_num)

end MathlibExtTest.Biology.Biophysics.SaturableElimination
