/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ViscositySolution.Comparison

open Filter Set Topology MathlibExt.Analysis.ViscositySolution
  MathlibExt.Analysis.ViscositySolutionWanted

namespace MathlibExtTest.Analysis.ViscositySolution

/-- For `F(x, r, p) = r - x` on `(-1, 1)`, compare a subsolution that jumps up at `0`
with a supersolution that jumps up immediately to its right. Both vanish on the frontier. -/
example (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (Ioo (-1 : ℝ) 0).indicator (fun _ => (-1 : ℝ)) x ≤
      (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x := by
  classical
  let Ω := Ioo (-1 : ℝ) 1
  let u := (Ioo (-1 : ℝ) 0).indicator (fun _ => (-1 : ℝ))
  let v := (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))
  let F (x' : ℝ) (r : ℝ) (_ : ℝ →L[ℝ] ℝ) := r - x'
  have hu : UpperSemicontinuous u := isOpen_Ioo.upperSemicontinuous_indicator (by norm_num)
  have hv : LowerSemicontinuous v := isOpen_Ioo.lowerSemicontinuous_indicator (by norm_num)
  have hsub : IsViscositySubsolution F Ω u := by
    refine ⟨hu.upperSemicontinuousOn _, fun y hy _ _ _ => ?_⟩
    change u y - y ≤ 0
    rcases lt_or_ge y 0 with h | h
    · simpa [u, indicator_of_mem (show y ∈ Ioo (-1 : ℝ) 0 from ⟨hy.1, h⟩)] using hy.1.le
    · simpa [u, indicator_of_notMem (show y ∉ Ioo (-1 : ℝ) 0 from fun hy' => h.not_gt hy'.2)]
        using h
  have hsup : IsViscositySupersolution F Ω v := by
    refine ⟨hv.lowerSemicontinuousOn _, fun y hy _ _ _ => ?_⟩
    change 0 ≤ v y - y
    rcases lt_or_ge 0 y with h | h
    · simpa [v, indicator_of_mem (show y ∈ Ioo (0 : ℝ) 1 from ⟨h, hy.2⟩)] using hy.2.le
    · simpa [v, indicator_of_notMem (show y ∉ Ioo (0 : ℝ) 1 from fun hy' => h.not_gt hy'.1)]
        using h
  have hbdry : ∀ y ∈ frontier Ω, u y ≤ v y := by
    intro y hy
    have hout : y ∉ Ω := ((isOpen_Ioo : IsOpen Ω).frontier_eq ▸ hy).2
    have huout : y ∉ Ioo (-1 : ℝ) 0 := fun hy' => hout ⟨hy'.1, hy'.2.trans zero_lt_one⟩
    have hvout : y ∉ Ioo (0 : ℝ) 1 := fun hy' => hout ⟨by linarith [hy'.1], hy'.2⟩
    simp [u, v, indicator_of_notMem huout, indicator_of_notMem hvout]
  refine le_of_isViscositySubsolution_of_isViscositySupersolution_of_structure
    (Ω := Ω) (hΩ := isOpen_Ioo) (hΩb := Metric.isBounded_Ioo (-1) 1) (F := F)
    (hF := (show Continuous (fun q : ℝ × ℝ × (ℝ →L[ℝ] ℝ) => F q.1 q.2.1 q.2.2) by
      dsimp [F]; fun_prop).continuousOn)
    (γ := 1) (hγ := one_pos) (hproper := ?_) (ω := id)
    (hω := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) (hω0 := fun _ h => h)
    (hstruct := ?_) (hu := hu.upperSemicontinuousOn _) (hv := hv.lowerSemicontinuousOn _)
    (hsub := hsub) (hsup := hsup) (hbdry := hbdry) x hx
  · intro y _ r s _ _
    dsimp [F]
    linarith
  · intro y _ z _ r α hα
    have hd := le_abs_self (y - z)
    have hp : 0 ≤ α * ‖y - z‖ ^ 2 := by positivity
    simp only [F, id_eq, Real.norm_eq_abs] at hp ⊢
    linarith

end MathlibExtTest.Analysis.ViscositySolution
