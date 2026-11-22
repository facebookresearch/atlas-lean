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
# Diffusive energy estimate

For a smooth periodic solution of `c_t + U * c_x = D * c_xx` on
`[0, L]` with `L > 0` and `D ≥ 0`,
`d/dt ∫_0^L c^2 / 2 = -D * ∫_0^L c_x^2 ≤ 0`.

The proof is conditional, with hypotheses indexed by the time `t` and
the points `x ∈ [0, L]`: `ct`, `cx`, `cxx` are the time, space, and
second-space derivatives given by `HasDerivAt` hypotheses at `t` and at
each `x ∈ [0, L]`, the PDE holds at `t` for each `x ∈ [0, L]`, `c t` and
`cx t` are periodic (equal values at `0` and `L`, so both boundary terms
vanish), and differentiation under the integral sign is a hypothesis
(`hInter`). The PDE is not assumed outside `[0, L]` or at other times.
The derivative hypotheses are full (two-sided) derivatives, so at the
endpoints `0` and `L` they also involve `c t` and `cx t` just outside
`[0, L]`, and the time derivatives involve times near `t`. No existence
result for arbitrary initial data is claimed. Energy here is squared-L2
concentration, not thermodynamic energy.

## Key results

- `energy_deriv`: the energy identity.
- `dissipation_nonpos`: the dissipation term `-D * ∫_0^L c_x^2` is nonpositive, so with
  `energy_deriv` the energy derivative at each `t` is `≤ 0`.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Analysis.PDE.DiffusiveEnergy

set_option linter.unusedVariables false in
/-- Diffusive energy identity: for a smooth periodic solution of
`c_t + U * c_x = D * c_xx` on `[0, L]`,
`d/dt ∫_0^L c^2 / 2 = -D * ∫_0^L c_x^2`.
`ct`, `cx`, `cxx` are the time, space, and second-space derivatives
of `c` at time `t`, given by the `HasDerivAt` hypotheses for
`x ∈ [0, L]` (full derivatives, so at `x = 0` and `x = L` they also
involve values just outside `[0, L]`); the PDE is assumed only at `t`
and for `x ∈ [0, L]`; `hInter` is the differentiation-under-the-integral
hypothesis (interchange regularity); periodicity is `c t` and `cx t`
taking equal values at `0` and `L`. This is a conditional identity, not
an existence result. -/
theorem energy_deriv {L D U : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (c ct cx cxx : ℝ → ℝ → ℝ) (t : ℝ)
    (hct : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun s => c s x) (ct t x) t)
    (hcx : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y => c t y) (cx t x) x)
    (hcxx : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y => cx t y) (cxx t x) x)
    (hPDE : ∀ x ∈ Set.uIcc 0 L, ct t x + U * cx t x = D * cxx t x)
    (hper_c : c t 0 = c t L) (hper_cx : cx t 0 = cx t L)
    (hInter : HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2)
      (∫ x in (0 : ℝ)..L, c t x * ct t x) t)
    (hInt_cxx : IntervalIntegrable (fun x => c t x * cxx t x) volume 0 L)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L)
    (hInt_ccx : IntervalIntegrable (fun x => c t x * cx t x) volume 0 L) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2)
      (-D * ∫ x in (0 : ℝ)..L, (cx t x) ^ 2) t := by
  have hmul : ∀ x ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun y => c t y * cx t y) ((cx t x) ^ 2 + c t x * cxx t x) x := by
    intro x hx
    have h := (hcx x hx).fun_mul (hcxx x hx)
    have hval : (cx t x) ^ 2 + c t x * cxx t x
        = cx t x * cx t x + c t x * cxx t x := by ring
    rw [hval]
    exact h
  have hsq : ∀ x ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun y => (c t y) ^ 2 / 2) (c t x * cx t x) x := by
    intro x hx
    have h := ((hcx x hx).fun_mul (hcx x hx)).div_const 2
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
    rw [hper_c, hper_cx, sub_self]
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
    rw [hper_c, sub_self]
  have hccx_zero : ∫ x in (0 : ℝ)..L, c t x * cx t x = 0 := by
    rw [hFTC2, hbc2]
  have hcongr : ∫ x in (0 : ℝ)..L, c t x * ct t x
      = ∫ x in (0 : ℝ)..L, ((-U) * (c t x * cx t x) + D * (c t x * cxx t x)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hct_eq : ct t x = D * cxx t x - U * cx t x := by
      linear_combination hPDE x hx
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
/-- Sign of the dissipation term of `energy_deriv`: `-D * ∫_0^L c_x^2 ≤ 0` for `D ≥ 0`. This is
only the sign of that term, not a monotonicity statement; combined with `energy_deriv` it shows
that the energy derivative at `t` is nonpositive. -/
theorem dissipation_nonpos {L D : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (cx : ℝ → ℝ → ℝ) (t : ℝ)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L) :
    -D * ∫ x in (0 : ℝ)..L, (cx t x) ^ 2 ≤ 0 := by
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..L, (cx t x) ^ 2 :=
    integral_nonneg_of_forall (le_of_lt hL) (fun u => sq_nonneg _)
  have hD' : -D ≤ 0 := neg_nonpos.mpr hD
  exact mul_nonpos_of_nonpos_of_nonneg hD' hnonneg


end MathlibExt.Analysis.PDE.DiffusiveEnergy
