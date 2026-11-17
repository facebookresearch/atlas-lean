/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exercise efficiency bound

For the declared power model `Pmet = Pbase + Pmech / eta` with
nonnegative baseline and mechanical powers and efficiency
`0 < eta ≤ 1`, metabolic power is at least the mechanical power, and
over an ordered finite window `a ≤ b` the metabolic energy cost is at
least the mechanical work. The window order matters: for `a > b` the
signed interval integral reverses the inequality.

This is a statement about the declared model only, with no diet,
patient-level or causal claim, and no calorie or FITT prescription.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace PhyslibExt.Biophysics.EnergyStores

/-- **Declared exercise-efficiency bound.** For the declared power model
`Pmet = Pbase + Pmech / eta` with nonnegative baseline and mechanical
powers and efficiency `eta ∈ (0, 1]`, metabolic power is at least the
mechanical power. -/
theorem exercise_efficiency_bound {Pbase Pmech eta : ℝ}
    (hbase : 0 ≤ Pbase) (hmech : 0 ≤ Pmech) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    Pmech ≤ Pbase + Pmech / eta := by
  have h : Pmech ≤ Pmech / eta := by
    rw [le_div_iff₀ heta0]
    calc Pmech * eta ≤ Pmech * 1 := mul_le_mul_of_nonneg_left heta1 hmech
      _ = Pmech := mul_one _
  linarith

/-- Integrated form: over any finite window, metabolic energy cost is at
least the mechanical work, when both powers are integrable and the
pointwise declared model holds. The window is `a ≤ b`; for `a > b` the
signed interval integral reverses the inequality. -/
theorem exercise_efficiency_integral {Pbase Pmech : ℝ → ℝ} {eta a b : ℝ}
    (hab : a ≤ b) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hbase : ∀ t, 0 ≤ Pbase t) (hmech : ∀ t, 0 ≤ Pmech t)
    (hint_base : IntervalIntegrable Pbase MeasureTheory.volume a b)
    (hint_mech : IntervalIntegrable Pmech MeasureTheory.volume a b) :
    ∫ t in a..b, Pmech t ≤ ∫ t in a..b, (Pbase t + Pmech t / eta) := by
  have hpt : Pmech ≤ fun t => Pbase t + Pmech t / eta :=
    fun t => exercise_efficiency_bound (hbase t) (hmech t) heta0 heta1
  exact intervalIntegral.integral_mono hab hint_mech
    (hint_base.add (hint_mech.div_const eta)) hpt

end PhyslibExt.Biophysics.EnergyStores
