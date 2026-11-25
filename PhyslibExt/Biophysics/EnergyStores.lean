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
* `energy_composition_perturbation`, `energy_composition_witness`:
  energy-preserving store perturbations change total mass.

## iii. Table of contents

* A. Pointwise efficiency bound.
* B. Integrated efficiency bound.
* C. Energy budget identity.
* D. Energy-preserving composition perturbation.

## iv. References

* The declared models are local to this module; no literature result
  is claimed, so all declarations are `lemma`s.

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
least the mechanical work, when both powers are integrable on the window,
nonnegative at every time, and `0 < eta ≤ 1`. The window is `a ≤ b`; for `a > b` the
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
`rhoL` (positive), stores `F`, `L` and component fluxes `qF`, `qL`
satisfying the separate component balances in derivative form on
the integration window (`rhoF * F` has derivative `qF` and
`rhoL * L` has derivative `qL` at every `s ∈ [0, t]`), and the net
balance `qF + qL = intake - expenditure` on the window, the stored
energy `E = rhoF * F + rhoL * L` satisfies
`E t - E 0 = ∫ s in 0..t, (intake s - expenditure s)`, for `t ≥ 0` and `intake - expenditure`
integrable on `[0, t]`. No variable-density or hydration term is present in this declared
model. -/
lemma energy_budget {rhoF rhoL : ℝ} {F L qF qL intake expenditure : ℝ → ℝ}
    {t : ℝ} (hrhoF : 0 < rhoF) (hrhoL : 0 < rhoL) (ht : 0 ≤ t)
    (hF : ∀ s ∈ Set.Icc 0 t, HasDerivAt (fun u => rhoF * F u) (qF s) s)
    (hL : ∀ s ∈ Set.Icc 0 t, HasDerivAt (fun u => rhoL * L u) (qL s) s)
    (hbal : ∀ s ∈ Set.Icc 0 t, qF s + qL s = intake s - expenditure s)
    (hint : IntervalIntegrable (fun s => intake s - expenditure s)
      MeasureTheory.volume 0 t) :
    (rhoF * F t + rhoL * L t) - (rhoF * F 0 + rhoL * L 0) =
      ∫ s in (0)..t, (intake s - expenditure s) := by
  have hE : ∀ s ∈ Set.Icc (0:ℝ) t,
      HasDerivAt (fun u => rhoF * F u + rhoL * L u) (qF s + qL s) s :=
    fun s hs => (hF s hs).add (hL s hs)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => rhoF * F u + rhoL * L u)
    (f' := fun s => intake s - expenditure s)
    (fun s hs => by
      have hs' : s ∈ Set.Icc (0:ℝ) t := by
        rwa [Set.uIcc_of_le ht] at hs
      rw [← hbal s hs']
      exact hE s hs') hint
  exact hftc.symm
/-! ## D. Energy-preserving composition perturbation. -/

/-- **Energy-preserving composition perturbation.** Perturbing the
stores `(F, L)` by `(rhoL * s, -rhoF * s)` preserves the stored
energy `rhoF * F + rhoL * L` exactly, while the total mass changes by
`(rhoL - rhoF) * s`. Hence, when `rhoF ≠ rhoL` and `s ≠ 0`, two
admissible compositions can share one energy with different masses:
energy alone does not identify the composition. -/
lemma energy_composition_perturbation {rhoF rhoL F L s : ℝ} :
    rhoF * (F + rhoL * s) + rhoL * (L - rhoF * s) = rhoF * F + rhoL * L ∧
    ((F + rhoL * s) + (L - rhoF * s)) - (F + L) = (rhoL - rhoF) * s := by
  constructor
  · ring
  · ring

/-- **Nonvacuous witness.** With `rhoF = 2`, `rhoL = 1`, the
compositions `(F, L) = (1, 2)` and `(3/2, 1)` both have stored energy
`4` but total masses `3` and `5/2`. -/
lemma energy_composition_witness :
    (2 : ℝ) * 1 + 1 * 2 = 4 ∧ (2 : ℝ) * (3 / 2) + 1 * 1 = 4 ∧
    (1 : ℝ) + 2 = 3 ∧ (3 / 2 : ℝ) + 1 = 5 / 2 ∧ (3 : ℝ) ≠ 5 / 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PhyslibExt.Biophysics.EnergyStores
