/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lower bound on freezing time from a latent-energy account

The lumped enthalpy model specifies the total heat to be removed. Integrating a
uniform bound on the net rate of heat removal gives a lower bound on the duration.
The rate bound is on heat extraction, not electrical input.
-/

open MeasureTheory

namespace Domains.Chemistry.ThermalBalances.FreezingTime

/-- Given the stated constant-pressure sensible and latent heat account, the heat `Q` to
remove is positive. If the net removal rate integrates to `Q` and is bounded by `Pmax`
on the time interval, the duration is at least `Q / Pmax`. This is a lower bound, not a
claim of attainability or a model of a moving phase boundary.

OpenStax, *University Physics Volume 2*, §1.5 supplies the phase-change and latent-heat
context. The lumped energy account is a hypothesis here. -/
public theorem freezing_time_lower_bound (m T₀ Tf Tend cl cs L Pmax duration : ℝ)
    (P : ℝ → ℝ) (hm : 0 < m) (hcl : 0 < cl) (hcs : 0 < cs) (hL : 0 < L)
    (hbefore : Tf ≤ T₀) (hafter : Tend ≤ Tf) (hPmax : 0 < Pmax) (hduration : 0 ≤ duration)
    (hIntegrable : IntervalIntegrable P volume 0 duration)
    (hcap : ∀ t ∈ Set.Icc 0 duration, 0 ≤ P t ∧ P t ≤ Pmax)
    (haccount : (∫ t in (0 : ℝ)..duration, P t) = m * (cl * (T₀ - Tf) + L + cs * (Tf - Tend))) :
    let Q := m * (cl * (T₀ - Tf) + L + cs * (Tf - Tend))
    0 < Q ∧ Q / Pmax ≤ duration := by
  dsimp only
  refine ⟨?_, (div_le_iff₀ hPmax).2 ?_⟩
  · exact mul_pos hm (add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos (mul_nonneg hcl.le (sub_nonneg.mpr hbefore)) hL)
      (mul_nonneg hcs.le (sub_nonneg.mpr hafter)))
  · have hle := intervalIntegral.integral_mono_on hduration hIntegrable
      (intervalIntegrable_const (c := Pmax)) (fun t ht => (hcap t ht).2)
    simpa only [haccount, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hle

end Domains.Chemistry.ThermalBalances.FreezingTime
