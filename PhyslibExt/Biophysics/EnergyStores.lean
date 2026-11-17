/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exercise efficiency and energy budget

## i. Overview

For the declared power model `Pmet = Pbase + Pmech / eta` with
nonnegative baseline and mechanical powers and efficiency
`0 < eta ≤ 1`, metabolic power is at least the mechanical power, and
over an ordered finite window `a ≤ b` the metabolic energy cost is at
least the mechanical work. The window order matters: for `a > b` the
signed interval integral reverses the inequality. The module also
proves the energy-budget identity: stored energy
`rhoF * F + rhoL * L` with derivative `intake - expenditure` changes
by exactly the net intake integral.

This is a statement about the declared model only, with no diet,
patient-level or causal claim, and no calorie or FITT prescription.

## ii. Key results

* `exercise_efficiency_bound`: the pointwise bound on metabolic power.
* `exercise_efficiency_integral`: the integrated bound over `a ≤ b`.
* `energy_budget`: stored-energy change equals net intake integral.

## iii. Table of contents

* A. Pointwise efficiency bound.
* B. Integrated efficiency bound.
* C. Energy budget identity.

## iv. References

* The declared models are local to this module; no literature result
  is claimed, so all three declarations are `lemma`s.

-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace PhyslibExt.Biophysics.EnergyStores

/-! ## A. Pointwise efficiency bound. -/

/-- **Declared exercise-efficiency bound.** For the declared power model
`Pmet = Pbase + Pmech / eta` with nonnegative baseline and mechanical
powers and efficiency `eta ∈ (0, 1]`, metabolic power is at least the
mechanical power. -/
lemma exercise_efficiency_bound {Pbase Pmech eta : ℝ}
    (hbase : 0 ≤ Pbase) (hmech : 0 ≤ Pmech) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    Pmech ≤ Pbase + Pmech / eta := by
  have h : Pmech ≤ Pmech / eta := by
    rw [le_div_iff₀ heta0]
    calc Pmech * eta ≤ Pmech * 1 := mul_le_mul_of_nonneg_left heta1 hmech
      _ = Pmech := mul_one _
  linarith

/-! ## B. Integrated efficiency bound. -/

/-- Integrated form: over any finite window, metabolic energy cost is at
least the mechanical work, when both powers are integrable and the
pointwise declared model holds. The window is `a ≤ b`; for `a > b` the
signed interval integral reverses the inequality. -/
lemma exercise_efficiency_integral {Pbase Pmech : ℝ → ℝ} {eta a b : ℝ}
    (hab : a ≤ b) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hbase : ∀ t, 0 ≤ Pbase t) (hmech : ∀ t, 0 ≤ Pmech t)
    (hint_base : IntervalIntegrable Pbase MeasureTheory.volume a b)
    (hint_mech : IntervalIntegrable Pmech MeasureTheory.volume a b) :
    ∫ t in a..b, Pmech t ≤ ∫ t in a..b, (Pbase t + Pmech t / eta) := by
  have hpt : Pmech ≤ fun t => Pbase t + Pmech t / eta :=
    fun t => exercise_efficiency_bound (hbase t) (hmech t) heta0 heta1
  exact intervalIntegral.integral_mono hab hint_mech
    (hint_base.add (hint_mech.div_const eta)) hpt

/-! ## C. Energy budget identity. -/

set_option linter.unusedVariables false in
/-- **Energy budget identity.** With fixed energy densities `rhoF`,
`rhoL` (positive), store trajectories `F`, `L` and component fluxes
`qF`, `qL` satisfying the component balances in derivative form
(`rhoF * F + rhoL * L` has derivative `qF + qL` everywhere), and the
net balance `qF + qL = intake - expenditure`, the stored energy
`E = rhoF * F + rhoL * L` satisfies
`E t - E 0 = ∫ s in 0..t, (intake s - expenditure s)`. No
variable-density or hydration term is present in this declared model. -/
lemma energy_budget {rhoF rhoL : ℝ} {F L qF qL intake expenditure : ℝ → ℝ}
    {t : ℝ} (hrhoF : 0 < rhoF) (hrhoL : 0 < rhoL) (ht : 0 ≤ t)
    (hE : ∀ s : ℝ, HasDerivAt (fun u => rhoF * F u + rhoL * L u) (qF s + qL s) s)
    (hbal : ∀ s : ℝ, qF s + qL s = intake s - expenditure s)
    (hint : IntervalIntegrable (fun s => intake s - expenditure s)
      MeasureTheory.volume 0 t) :
    (rhoF * F t + rhoL * L t) - (rhoF * F 0 + rhoL * L 0) =
      ∫ s in (0)..t, (intake s - expenditure s) := by
  have hfun : (fun s => qF s + qL s) = (fun s => intake s - expenditure s) :=
    funext hbal
  have hint' : IntervalIntegrable (fun s => qF s + qL s) MeasureTheory.volume 0 t := by
    rw [hfun]
    exact hint
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => rhoF * F u + rhoL * L u) (f' := fun s => qF s + qL s)
    (fun s _ => hE s) hint'
  rw [← hfun]
  exact hftc.symm

end PhyslibExt.Biophysics.EnergyStores
