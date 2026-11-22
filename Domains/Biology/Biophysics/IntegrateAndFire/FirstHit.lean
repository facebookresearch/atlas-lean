/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order.Basic

/-!
# Leaky integrate-and-fire first threshold hit

For the trajectory `u(t) = uinf - (uinf - ur) * exp (-t / tau)` from
reset `ur` toward the steady value `uinf` under constant drive, with
`ur < theta`, `tau > 0` and `uinf > theta`, the first hit of the
threshold `theta` is `T = tau * log ((uinf - ur) / (uinf - theta))`:
positive, exact (`u(T) = theta`), and first (`u(t) < theta` before
`T`). If `uinf ≤ theta` there is no finite hit; at `uinf = theta` the
approach is asymptotic only.

This is the declared scalar trajectory only: no Hodgkin-Huxley
reduction and no spiking-network claim.
-/

@[expose] public section

open Real
open Topology Filter

namespace MathlibExt.Biology.Biophysics.IntegrateAndFire.FirstHit

/-- **Leaky integrate-and-fire first hit.** For the trajectory
`u(t) = uinf - (uinf - ur) * exp (-t / tau)` from reset `ur` toward
`uinf`, with `ur < theta`, `tau > 0` and `uinf > theta`, the first
threshold hit is `T = tau * log ((uinf - ur) / (uinf - theta)) > 0`:
`u(T) = theta` and `u(t) < theta` for `0 ≤ t < T`. -/
theorem lif_first_hit {ur theta tau uinf : ℝ}
    (hur : ur < theta) (htau : 0 < tau) (hu : theta < uinf) :
    let T := tau * Real.log ((uinf - ur) / (uinf - theta))
    0 < T ∧ uinf - (uinf - ur) * Real.exp (-T / tau) = theta ∧
    ∀ t : ℝ, 0 ≤ t → t < T →
      uinf - (uinf - ur) * Real.exp (-t / tau) < theta := by
  have h1 : 0 < uinf - theta := sub_pos.mpr hu
  have h2 : 0 < uinf - ur := by linarith
  have h1ne : uinf - theta ≠ 0 := ne_of_gt h1
  have h2ne : uinf - ur ≠ 0 := ne_of_gt h2
  have htau_ne : tau ≠ 0 := ne_of_gt htau
  have hratio : 1 < (uinf - ur) / (uinf - theta) := by
    rw [one_lt_div h1]
    linarith
  have hlog : 0 < Real.log ((uinf - ur) / (uinf - theta)) := Real.log_pos hratio
  have hratio_pos : 0 < (uinf - ur) / (uinf - theta) := div_pos h2 h1
  have hT : 0 < tau * Real.log ((uinf - ur) / (uinf - theta)) := mul_pos htau hlog
  have hTT : -(tau * Real.log ((uinf - ur) / (uinf - theta))) / tau
      = -Real.log ((uinf - ur) / (uinf - theta)) := by
    rw [neg_div, mul_div_cancel_left₀ _ htau_ne]
  have hexp : Real.exp (-Real.log ((uinf - ur) / (uinf - theta)))
      = (uinf - theta) / (uinf - ur) := by
    rw [Real.exp_neg, Real.exp_log hratio_pos, inv_div]
  refine ⟨hT, ?_, ?_⟩
  · rw [hTT, hexp]
    field_simp
    ring
  · intro t _ htT
    have hdiv : t / tau < (tau * Real.log ((uinf - ur) / (uinf - theta))) / tau :=
      div_lt_div_of_pos_right htT htau
    have harg : -(tau * Real.log ((uinf - ur) / (uinf - theta))) / tau < -t / tau := by
      rw [neg_div, neg_div]
      exact neg_lt_neg hdiv
    have hmono : Real.exp (-(tau * Real.log ((uinf - ur) / (uinf - theta))) / tau)
        < Real.exp (-t / tau) := Real.exp_lt_exp.mpr harg
    rw [hTT, hexp] at hmono
    have hmul := mul_lt_mul_of_pos_right hmono h2
    rw [div_mul_cancel₀ _ h2ne] at hmul
    have hcomm : (uinf - ur) * Real.exp (-t / tau)
        = Real.exp (-t / tau) * (uinf - ur) := mul_comm _ _
    linarith

set_option linter.unusedVariables false in
/-- **No finite hit at or below threshold equilibrium.** If
`ur < uinf ≤ theta` and `tau > 0`, the trajectory stays strictly
below `theta` at every finite `t ≥ 0`; at `uinf = theta` the approach
is asymptotic only. -/
theorem lif_no_hit {ur theta tau uinf : ℝ}
    (hur : ur < uinf) (htau : 0 < tau) (hu : uinf ≤ theta) :
    ∀ t : ℝ, 0 ≤ t → uinf - (uinf - ur) * Real.exp (-t / tau) < theta := by
  intro t _
  have hpos : 0 < (uinf - ur) * Real.exp (-t / tau) :=
    mul_pos (sub_pos.mpr hur) (Real.exp_pos _)
  linarith

/-- **Asymptotic approach at threshold equilibrium.** At
`uinf = theta` with `tau > 0`, the trajectory
`theta - (theta - ur) * exp (-t / tau)` tends to `theta` as
`t → ∞`; when additionally `ur < theta` it does not attain `theta`
at any finite time (`lif_no_hit`). -/
theorem lif_tendsto {ur theta tau : ℝ} (htau : 0 < tau) :
    Filter.Tendsto (fun t => theta - (theta - ur) * Real.exp (-t / tau))
      Filter.atTop (𝓝 theta) := by
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-t / tau)) Filter.atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have h1 : Filter.Tendsto (fun t : ℝ => t / tau) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_div_const htau Filter.tendsto_id
    have h2 : Filter.Tendsto (fun t : ℝ => -(t / tau)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h1
    exact h2.congr (fun t => by ring)
  have h2 := hexp.const_mul (theta - ur)
  simpa using (Filter.Tendsto.const_sub theta h2)

end MathlibExt.Biology.Biophysics.IntegrateAndFire.FirstHit
