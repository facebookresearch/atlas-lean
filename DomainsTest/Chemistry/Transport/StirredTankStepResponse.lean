/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Chemistry.Transport.StirredTankStepResponse
import Mathlib.Tactic.NormNum

/-! # Boundary checks for the ideal stirred-tank step response -/

open Chemistry.Transport Engineering.Process.CSTR Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

private noncomputable abbrev response (k t : ℝ) : ℝ :=
  if 0 ≤ t then solution 2 3 k 4 0 t / 4 else 0

local notation "responseSpec" => stirredTankStepResponse (V := 2) (Q := 3) (cin := 4)
  (by norm_num) (by norm_num) (by norm_num)

-- The zero extension and the Mathlib density both vanish at negative time.
example : response 0 (-1) = 0 ∧ exponentialPDFReal (3 / 2) (-1) = 0 := by
  obtain ⟨_, hcdf, hpdf, _⟩ := responseSpec
  change response 0 = (cdf (expMeasure (3 / 2)) : ℝ → ℝ) at hcdf
  constructor
  · rw [congrFun hcdf (-1), cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  · rw [hpdf (-1)]
    norm_num

-- At the step onset the response is zero, and the PDF gives only the right derivative.
example : response 0 0 = 0 ∧ HasDerivWithinAt (response 0) (3 / 2) (Ici 0) 0 ∧
    ¬ DifferentiableAt ℝ (response 0) 0 := by
  obtain ⟨_, hcdf, hpdf, _, hright, hnotDiff, _⟩ := responseSpec
  change response 0 = (cdf (expMeasure (3 / 2)) : ℝ → ℝ) at hcdf
  refine ⟨?_, ?_, hnotDiff⟩
  · rw [congrFun hcdf 0, cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  · rw [hpdf 0] at hright
    simpa using hright

-- Away from the onset the two-sided derivative agrees with the explicit density.
example : HasDerivAt (response 0) ((3 / 2) * Real.exp (-(3 / 2))) 1 := by
  obtain ⟨_, _, hpdf, hderiv, _⟩ := responseSpec
  have h := hderiv 1 (by norm_num)
  rw [hpdf 1] at h
  simpa using h

-- For positive loss the deficit is genuine: no probability measure has this CDF.
example (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Tendsto (response 2) atTop (𝓝 (3 / 7)) ∧ (3 / 7 : ℝ) < 1 ∧
      response 2 ≠ (cdf μ : ℝ → ℝ) := by
  obtain ⟨_, _, _, _, _, _, hloss⟩ := responseSpec
  obtain ⟨hlim, hlt, hnotCdf⟩ := hloss 2 (by norm_num)
  have hval : (3 : ℝ) / (3 + 2 * 2) = 3 / 7 := by norm_num
  rw [hval] at hlim hlt
  exact ⟨hlim, hlt, hnotCdf μ⟩
