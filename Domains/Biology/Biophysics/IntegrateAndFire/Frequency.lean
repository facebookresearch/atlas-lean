/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Monotone.Basic
public import Domains.Biology.Biophysics.IntegrateAndFire.FirstHit

/-!
# LIF firing frequency

For the scalar leaky integrate-and-fire trajectory, the first-hit
period is `tau log ((uinf - ur)/(uinf - theta))` on the
superthreshold domain, and the firing frequency `1/(T + tref)` is
strictly increasing in drive, hence in current under an affine
drive-current relation with `R > 0`. The period definition is
shared with `IntegrateAndFire.FirstHit.lif_first_hit`.

Provenance: the scalar LIF closed form and its log period are the
declared forms of `IntegrateAndFire.FirstHit`; `tau` is a time
constant, `ur`, `theta`, `uinf` are voltages in common units.
-/

@[expose] public section

open Real

namespace MathlibExt.Biology.Biophysics.IntegrateAndFire.Frequency

/-- **LIF period.** For `tau > 0` and superthreshold drive
`uinf > theta > ur`, the first-hit period of the scalar trajectory
`u(t) = uinf - (uinf - ur) * exp (-t / tau)` from reset `ur` to
threshold `theta` is `T = tau * log ((uinf - ur) / (uinf - theta))`,
which is positive. Outside that domain the formula follows the
conventions `x / 0 = 0`, `log 0 = 0` and `log x = log |x|`; for
example it is `0` when `uinf = theta`. -/
noncomputable def lifPeriod (tau ur theta uinf : ℝ) : ℝ :=
  tau * Real.log ((uinf - ur) / (uinf - theta))

/-- For `tau > 0`, the period is positive on the superthreshold domain `ur < theta < uinf`. -/
lemma lifPeriod_pos {tau ur theta uinf : ℝ} (htau : 0 < tau)
    (hur : ur < theta) (hu : theta < uinf) : 0 < lifPeriod tau ur theta uinf := by
  exact (MathlibExt.Biology.Biophysics.IntegrateAndFire.FirstHit.lif_first_hit
    hur htau hu).1

/-- **Frequency increases with drive.** The firing frequency
`1 / (T(uinf) + tref)` with `tref ≥ 0` is strictly increasing in the
superthreshold drive `uinf` (at fixed `ur < theta`, `tau > 0`). -/
lemma lif_frequency_strictMonoOn {tau ur theta tref : ℝ} (htau : 0 < tau)
    (hur : ur < theta) (htref : 0 ≤ tref) :
    StrictMonoOn (fun uinf => 1 / (lifPeriod tau ur theta uinf + tref))
      (Set.Ioi theta) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hTa : 0 < lifPeriod tau ur theta a := lifPeriod_pos htau hur ha
  have hTb : 0 < lifPeriod tau ur theta b := lifPeriod_pos htau hur hb
  have ha_pos : 0 < a - theta := by linarith
  have hb_pos : 0 < b - theta := by linarith
  have ha_ur : 0 < a - ur := by linarith
  have hb_ur : 0 < b - ur := by linarith
  have hdiv : (b - ur) / (b - theta) < (a - ur) / (a - theta) := by
    rw [div_lt_div_iff₀ hb_pos ha_pos]
    have hprod : 0 < (b - a) * (theta - ur) :=
      mul_pos (sub_pos.mpr hab) (sub_pos.mpr hur)
    nlinarith [hprod]
  have hlog : Real.log ((b - ur) / (b - theta)) < Real.log ((a - ur) / (a - theta)) :=
    Real.log_lt_log (div_pos hb_ur hb_pos) hdiv
  have hT : lifPeriod tau ur theta b < lifPeriod tau ur theta a := by
    unfold lifPeriod
    exact mul_lt_mul_of_pos_left hlog htau
  have hden_lt : lifPeriod tau ur theta b + tref < lifPeriod tau ur theta a + tref := by
    linarith
  have hden_pos : 0 < lifPeriod tau ur theta b + tref := by linarith
  exact one_div_lt_one_div_of_lt hden_pos hden_lt

/-- **Frequency increases with current.** For `tau > 0`, `ur < theta`, `tref ≥ 0`,
`uinf = urest + R * I` and fixed `R > 0`, the frequency is strictly increasing in current `I` on the
superthreshold current range `theta < urest + R * I`. -/
lemma lif_frequency_current_strictMonoOn {tau ur theta tref urest R : ℝ}
    (htau : 0 < tau) (hur : ur < theta) (htref : 0 ≤ tref) (hR : 0 < R) :
    StrictMonoOn (fun I => 1 / (lifPeriod tau ur theta (urest + R * I) + tref))
      {I | theta < urest + R * I} := by
  intro a ha b hb hab
  have hmono := lif_frequency_strictMonoOn htau hur htref
  have hult : urest + R * a < urest + R * b := by
    have hRmul : R * a < R * b := mul_lt_mul_of_pos_left hab hR
    linarith
  exact hmono ha hb hult

end MathlibExt.Biology.Biophysics.IntegrateAndFire.Frequency
