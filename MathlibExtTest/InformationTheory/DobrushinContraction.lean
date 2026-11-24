/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DobrushinContraction

@[expose] public section

/-!
# Tests for Dobrushin's contraction coefficient

* A constant kernel has coefficient `0`, so it maps every pair of inputs to the same output law.
* The identity kernel on `Bool` has coefficient `1`: no contraction.
* The data-processing inequality for total variation, instantiated.
-/

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.DobrushinContraction

namespace MathlibExtTest.InformationTheory.DobrushinContraction

/-- A constant kernel has Dobrushin coefficient `0`. -/
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ρ : Measure Y)
    [IsProbabilityMeasure ρ] : dobrushinCoeff (Kernel.const X ρ) = 0 := by
  simp [dobrushinCoeff, totalVariationDist_self]

/-- Hence a constant kernel maps any two inputs to output laws at total variation `0`. -/
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ρ : Measure Y)
    [IsProbabilityMeasure ρ] (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    totalVariationDist (Kernel.const X ρ ∘ₘ μ) (Kernel.const X ρ ∘ₘ ν) ≤ 0 := by
  have h := totalVariationDist_comp_le (Kernel.const X ρ) μ ν
  have h0 : dobrushinCoeff (Kernel.const X ρ) = 0 := by
    simp [dobrushinCoeff, totalVariationDist_self]
  rwa [h0, zero_mul] at h

/-- The identity kernel on `Bool` has Dobrushin coefficient `1`. -/
example : dobrushinCoeff (Kernel.id : Kernel Bool Bool) = 1 := by
  classical
  refine le_antisymm (dobrushinCoeff_mem_Icc _).2 ?_
  have h := totalVariationDist_le_dobrushinCoeff (Kernel.id : Kernel Bool Bool) true false
  simpa [Kernel.id_apply, totalVariationDist_dirac] using h

/-- Data processing for total variation. -/
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (κ : Kernel X Y)
    [IsMarkovKernel κ] (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariationDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ totalVariationDist μ ν :=
  totalVariationDist_comp_le_self κ μ ν

end MathlibExtTest.InformationTheory.DobrushinContraction
