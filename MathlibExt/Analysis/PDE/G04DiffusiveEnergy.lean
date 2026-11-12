/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Diffusive energy estimate (G04)

For a smooth periodic solution of `c_t + U * c_x = D * c_xx` on
`[0, L]` with `L > 0` and `D ≥ 0`,
`d/dt ∫_0^L c^2 / 2 = -D * ∫_0^L c_x^2 ≤ 0`.

The proof is conditional: `ct`, `cx`, `cxx` are the time, space, and
second-space derivatives given by `HasDerivAt` hypotheses, the PDE
holds pointwise, `c` and `cx` are periodic (equal values at `0` and
`L`, so both boundary terms vanish), and differentiation under the
integral sign is a hypothesis (`hInter`). No existence result for
arbitrary initial data is claimed. Energy here is squared-L2
concentration, not thermodynamic energy.

## Key results

- `g04_energy_deriv`: the energy identity.
- `g04_energy_nonpos`: the energy is nonincreasing.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Analysis.PDE.G04DiffusiveEnergy

set_option linter.unusedVariables false in
/-- Diffusive energy identity: for a smooth periodic solution of
`c_t + U * c_x = D * c_xx` on `[0, L]`,
`d/dt ∫_0^L c^2 / 2 = -D * ∫_0^L c_x^2`.
`ct`, `cx`, `cxx` are the time, space, and second-space derivatives
of `c`, given by the `HasDerivAt` hypotheses; `hInter` is the
differentiation-under-the-integral hypothesis (interchange
regularity); periodicity is `c` and `cx` taking equal values at
`0` and `L`. This is a conditional identity, not an existence
result. -/
theorem g04_energy_deriv {L D U : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (c ct cx cxx : ℝ → ℝ → ℝ) (t : ℝ)
    (hct : ∀ t x, HasDerivAt (fun s => c s x) (ct t x) t)
    (hcx : ∀ t x, HasDerivAt (fun y => c t y) (cx t x) x)
    (hcxx : ∀ t x, HasDerivAt (fun y => cx t y) (cxx t x) x)
    (hPDE : ∀ t x, ct t x + U * cx t x = D * cxx t x)
    (hper_c : ∀ t, c t 0 = c t L) (hper_cx : ∀ t, cx t 0 = cx t L)
    (hInter : HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2)
      (∫ x in (0 : ℝ)..L, c t x * ct t x) t)
    (hInt_cxx : IntervalIntegrable (fun x => c t x * cxx t x) volume 0 L)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L)
    (hInt_ccx : IntervalIntegrable (fun x => c t x * cx t x) volume 0 L) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2)
      (-D * ∫ x in (0 : ℝ)..L, (cx t x) ^ 2) t := by
  have hmul : ∀ x ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun y => c t y * cx t y) ((cx t x) ^ 2 + c t x * cxx t x) x := by
    intro x _
    have h := (hcx t x).fun_mul (hcxx t x)
    have hval : (cx t x) ^ 2 + c t x * cxx t x
        = cx t x * cx t x + c t x * cxx t x := by ring
    rw [hval]
    exact h
  have hsq : ∀ x ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun y => (c t y) ^ 2 / 2) (c t x * cx t x) x := by
    intro x _
    have h := ((hcx t x).fun_mul (hcx t x)).div_const 2
    have hval : c t x * cx t x = (cx t x * c t x + c t x * cx t x) / 2 := by ring
    simp only [pow_two]
    rw [hval]
    exact h
  have hInt_sum : IntervalIntegrable (fun x => (cx t x) ^ 2 + c t x * cxx t x)
      volume 0 L := hInt_cx2.add hInt_cxx
  have hFTC1 : ∫ y in (0 : ℝ)..L, ((cx t y) ^ 2 + c t y * cxx t y)
      = c t L * cx t L - c t 0 * cx t 0 :=
    integral_eq_sub_of_hasDerivAt hmul hInt_sum
  have hbc1 : c t L * cx t L - c t 0 * cx t 0 = 0 := by
    rw [hper_c t, hper_cx t, sub_self]
  have hadd1 : ∫ x in (0 : ℝ)..L, ((cx t x) ^ 2 + c t x * cxx t x)
      = (∫ x in (0 : ℝ)..L, (cx t x) ^ 2) + ∫ x in (0 : ℝ)..L, c t x * cxx t x :=
    integral_add hInt_cx2 hInt_cxx
  have hcxx_eq : ∫ x in (0 : ℝ)..L, c t x * cxx t x
      = -∫ x in (0 : ℝ)..L, (cx t x) ^ 2 := by
    have h0 : (∫ x in (0 : ℝ)..L, (cx t x) ^ 2)
        + ∫ x in (0 : ℝ)..L, c t x * cxx t x = 0 := by
      rw [← hadd1, hFTC1, hbc1]
    linarith
  have hFTC2 : ∫ y in (0 : ℝ)..L, c t y * cx t y
      = (c t L) ^ 2 / 2 - (c t 0) ^ 2 / 2 :=
    integral_eq_sub_of_hasDerivAt hsq hInt_ccx
  have hbc2 : (c t L) ^ 2 / 2 - (c t 0) ^ 2 / 2 = 0 := by
    rw [hper_c t, sub_self]
  have hccx_zero : ∫ x in (0 : ℝ)..L, c t x * cx t x = 0 := by
    rw [hFTC2, hbc2]
  have hcongr : ∫ x in (0 : ℝ)..L, c t x * ct t x
      = ∫ x in (0 : ℝ)..L, ((-U) * (c t x * cx t x) + D * (c t x * cxx t x)) := by
    apply integral_congr_ae_restrict
    refine Filter.Eventually.of_forall (fun x => ?_)
    change c t x * ct t x = (-U) * (c t x * cx t x) + D * (c t x * cxx t x)
    have hct_eq : ct t x = D * cxx t x - U * cx t x := by
      linear_combination hPDE t x
    rw [hct_eq]
    ring
  have hIntA : IntervalIntegrable (fun x => (-U) * (c t x * cx t x)) volume 0 L :=
    hInt_ccx.const_mul (-U)
  have hIntB : IntervalIntegrable (fun x => D * (c t x * cxx t x)) volume 0 L :=
    hInt_cxx.const_mul D
  have hadd2 : ∫ x in (0 : ℝ)..L, ((-U) * (c t x * cx t x) + D * (c t x * cxx t x))
      = (∫ x in (0 : ℝ)..L, (-U) * (c t x * cx t x))
        + ∫ x in (0 : ℝ)..L, D * (c t x * cxx t x) :=
    integral_add hIntA hIntB
  have hmain : ∫ x in (0 : ℝ)..L, c t x * ct t x
      = -D * ∫ x in (0 : ℝ)..L, (cx t x) ^ 2 := by
    rw [hcongr, hadd2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hccx_zero, hcxx_eq]
    ring
  rw [hmain] at hInter
  exact hInter

set_option linter.unusedVariables false in
/-- The diffusive energy is nonincreasing: `-D * ∫ c_x^2 ≤ 0` for `D ≥ 0`. -/
theorem g04_energy_nonpos {L D : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (cx : ℝ → ℝ → ℝ) (t : ℝ)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L) :
    -D * ∫ x in (0 : ℝ)..L, (cx t x) ^ 2 ≤ 0 := by
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..L, (cx t x) ^ 2 :=
    integral_nonneg_of_forall (le_of_lt hL) (fun u => sq_nonneg _)
  have hD' : -D ≤ 0 := neg_nonpos.mpr hD
  exact mul_nonpos_of_nonpos_of_nonneg hD' hnonneg


end MathlibExt.Analysis.PDE.G04DiffusiveEnergy
