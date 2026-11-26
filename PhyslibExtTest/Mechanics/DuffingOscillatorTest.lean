/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.DuffingOscillator
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Hardening Duffing oscillator checks

Concrete consumers of `PhyslibExt.Mechanics.DuffingOscillator`: the hardening oscillator
`m = c = k = β = 1` released from the displaced state `(1, 0)`, the undamped case `c = 0`, and
the softening case `β = -1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Displaced, undamped and softening oscillators

## iv. References

None.

## A. Displaced, undamped and softening oscillators

-/

open Filter Set Topology Mechanics.DuffingOscillator

/-- Nonzero initial displacement: for `m = c = k = β = 1` the state `(1, 0)` (energy `3 / 4`) has
a forward solution that stays in its sublevel set and tends to the origin. -/
example :
    ∃ γ : ℝ → ℝ × ℝ, IsIntegralCurveOn γ (fun _ => duffingField 1 1 1 1) (Ici 0) ∧
      γ 0 = (1, 0) ∧ (∀ t, 0 ≤ t → duffingEnergy 1 1 1 (γ t) ≤ 3 / 4) ∧
      Tendsto γ atTop (𝓝 0) := by
  obtain ⟨γ, hγ, hγ0, hγS⟩ := isForwardInvariant_duffingSublevel (m := 1) (c := 1) (k := 1)
    (β := 1) one_pos one_pos one_pos zero_le_one (3 / 4) (1, 0)
    (by change duffingEnergy 1 1 1 (1, 0) ≤ 3 / 4; norm_num [duffingEnergy])
  exact ⟨γ, hγ, hγ0, hγS, tendsto_zero_of_isIntegralCurveOn one_pos one_pos one_pos one_pos hγ⟩

/-- No damping, no convergence: for `c = 0` (`m = k = β = 1`) the forward solution from `(1, 0)`
keeps the energy `3 / 4` and does not tend to the origin. -/
example :
    ∃ γ : ℝ → ℝ × ℝ, IsIntegralCurveOn γ (fun _ => duffingField 1 0 1 1) (Ici 0) ∧
      γ 0 = (1, 0) ∧ (∀ t, 0 ≤ t → duffingEnergy 1 1 1 (γ t) = 3 / 4) ∧
      ¬ Tendsto γ atTop (𝓝 0) := by
  obtain ⟨γ, hγ, hγ0, -⟩ := isForwardInvariant_duffingSublevel (m := 1) (c := 0) (k := 1)
    (β := 1) one_pos one_pos one_pos le_rfl (3 / 4) (1, 0)
    (by change duffingEnergy 1 1 1 (1, 0) ≤ 3 / 4; norm_num [duffingEnergy])
  have hanti := duffingEnergy_antitoneOn one_pos le_rfl hγ
  have hmono : MonotoneOn (fun t => duffingEnergy 1 1 1 (γ t)) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => duffingEnergyDeriv 1 1 1 (γ t) (duffingField 1 0 1 1 (γ t))) (convex_Ici 0)
      (fun t ht => (hasFDerivAt_duffingEnergy 1 1 1 (γ t)).continuousAt.comp_continuousWithinAt
        (hγ.continuousWithinAt ht)) (fun t ht => ?_) (fun t _ => ?_)
    · rw [interior_Ici] at ht
      exact ((hasFDerivAt_duffingEnergy 1 1 1 (γ t)).comp_hasDerivWithinAt t
        (hγ t (Set.mem_Ici.mpr (le_of_lt ht)))).mono interior_subset
    · rw [duffingEnergy_orbital one_pos]
      simp
  have hE0 : duffingEnergy 1 1 1 (γ 0) = 3 / 4 := by
    rw [hγ0]
    norm_num [duffingEnergy]
  have hconst : ∀ t, 0 ≤ t → duffingEnergy 1 1 1 (γ t) = 3 / 4 := by
    intro t ht
    have h1 := hanti (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr ht) ht
    have h2 := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr ht) ht
    dsimp only at h1 h2
    linarith
  refine ⟨γ, hγ, hγ0, hconst, fun hlim => ?_⟩
  have hVc : Continuous (duffingEnergy 1 1 1) := by
    unfold duffingEnergy
    fun_prop
  have h1 : Tendsto (fun t => duffingEnergy 1 1 1 (γ t)) atTop (𝓝 (duffingEnergy 1 1 1 0)) :=
    (hVc.tendsto 0).comp hlim
  have h2 : Tendsto (fun t => duffingEnergy 1 1 1 (γ t)) atTop (𝓝 (3 / 4)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hconst t ht).symm
  have := tendsto_nhds_unique h1 h2
  norm_num [duffingEnergy] at this

/-- Softening spring, `β = -1` (`m = c = k = 1`): the sublevel set `{V ≤ 0}` is not compact, and
the equilibrium `(1, 0)` is a solution that does not tend to the origin. -/
example :
    ¬ IsCompact {p : ℝ × ℝ | duffingEnergy 1 1 (-1) p ≤ 0} ∧
      IsIntegralCurveOn (fun _ => ((1 : ℝ), (0 : ℝ))) (fun _ => duffingField 1 1 1 (-1)) (Ici 0) ∧
      ¬ Tendsto (fun _ : ℝ => ((1 : ℝ), (0 : ℝ))) atTop (𝓝 0) := by
  refine ⟨fun hcpt => ?_, fun t _ => ?_, ?_⟩
  · obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hcpt.isBounded
    have hxpos : 0 < |R| + 2 := by positivity
    have hx : 2 ≤ (|R| + 2) ^ 2 := by nlinarith [abs_nonneg R]
    have hmem : ((|R| + 2, 0) : ℝ × ℝ) ∈ {p : ℝ × ℝ | duffingEnergy 1 1 (-1) p ≤ 0} := by
      change duffingEnergy 1 1 (-1) (|R| + 2, 0) ≤ 0
      simp only [duffingEnergy]
      nlinarith [mul_nonneg (sq_nonneg (|R| + 2)) (sub_nonneg.mpr hx)]
    have hn : ‖((|R| + 2, 0) : ℝ × ℝ)‖ = |R| + 2 := by
      rw [Prod.norm_def]
      simp [abs_of_pos hxpos, hxpos.le]
    have := hR _ hmem
    rw [hn] at this
    linarith [le_abs_self R]
  · have hf : duffingField 1 1 1 (-1) ((1 : ℝ), (0 : ℝ)) = 0 := by
      simp [duffingField]
    change HasDerivWithinAt (fun _ => ((1 : ℝ), (0 : ℝ))) (duffingField 1 1 1 (-1) (1, 0))
      (Ici 0) t
    rw [hf]
    exact hasDerivWithinAt_const _ _ _
  · rw [tendsto_const_nhds_iff]
    simp
