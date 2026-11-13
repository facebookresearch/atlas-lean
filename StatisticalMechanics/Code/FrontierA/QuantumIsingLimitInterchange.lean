/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecificLimits.Basic










open Filter

namespace StatMech.FrontierA




theorem quantumIsing_tendsto_of_uniform_cylinder_bound
    (trotterThermodynamic finiteQuantum : ℕ → ℝ)
    (finiteTrotter : ℕ → ℕ → ℝ) (freeEnergy : ℝ)
    (hfinite : ∀ L,
      Tendsto (finiteTrotter L) atTop (nhds (finiteQuantum L)))
    (hquantum : Tendsto finiteQuantum atTop (nhds freeEnergy))
    (huniform : ∀ L n,
      |trotterThermodynamic n - finiteTrotter L n| ≤
        1 / (2 * ((L : ℝ) + 1))) :
    Tendsto trotterThermodynamic atTop (nhds freeEnergy) := by
  have herr : Tendsto (fun L : ℕ => 1 / (2 * ((L : ℝ) + 1)))
      atTop (nhds 0) := by
    have hone := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hhalf := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2))).mul hone
    have hhalf' : Tendsto
        (fun L : ℕ => (1 / 2 : ℝ) * (1 / ((L : ℝ) + 1)))
        atTop (nhds 0) := by
      simpa using hhalf
    convert hhalf' using 1
    funext L
    field_simp [show (2 : ℝ) ≠ 0 by norm_num,
      show (L : ℝ) + 1 ≠ 0 by positivity]
  rw [Metric.tendsto_atTop] at hquantum herr ⊢
  intro epsilon hepsilon
  have hepsilonThird : 0 < epsilon / 3 := by positivity
  obtain ⟨Lquantum, hLquantum⟩ := hquantum (epsilon / 3) hepsilonThird
  obtain ⟨Lerror, hLerror⟩ := herr (epsilon / 3) hepsilonThird
  let L := max Lquantum Lerror
  have hq : |finiteQuantum L - freeEnergy| < epsilon / 3 := by
    rw [← Real.dist_eq]
    exact hLquantum L (le_max_left _ _)
  have he : 1 / (2 * ((L : ℝ) + 1)) < epsilon / 3 := by
    have h := hLerror L (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg] at h
    · exact h
    · positivity
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp (hfinite L)) (epsilon / 3) hepsilonThird
  refine ⟨N, fun n hn => ?_⟩
  have hf : |finiteTrotter L n - finiteQuantum L| < epsilon / 3 := by
    rw [← Real.dist_eq]
    exact hN n hn
  have hu := huniform L n
  have hu' : |trotterThermodynamic n - finiteTrotter L n| < epsilon / 3 :=
    lt_of_le_of_lt hu he
  rw [Real.dist_eq]
  calc
    |trotterThermodynamic n - freeEnergy| ≤
        |trotterThermodynamic n - finiteTrotter L n| +
          |finiteTrotter L n - finiteQuantum L| +
          |finiteQuantum L - freeEnergy| := by
      calc
        |trotterThermodynamic n - freeEnergy| ≤
            |trotterThermodynamic n - finiteTrotter L n| +
              |finiteTrotter L n - freeEnergy| := abs_sub_le _ _ _
        _ ≤ |trotterThermodynamic n - finiteTrotter L n| +
            (|finiteTrotter L n - finiteQuantum L| +
              |finiteQuantum L - freeEnergy|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ = _ := by ring
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
      gcongr
    _ = epsilon := by ring

end StatMech.FrontierA
