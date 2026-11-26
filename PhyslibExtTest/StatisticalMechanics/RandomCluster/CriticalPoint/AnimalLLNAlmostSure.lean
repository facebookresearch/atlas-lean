/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNAlmostSure

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNAlmostSure`

* `animalValue` of the constant environment `ω ≡ 1` at length `3` is `3` (via
  `prefix_le_animalValue` and `animalValue_le_iff`);
* `shiftEnv_measurePreserving` for the i.i.d. law `δ₁`;
* `animalValue_lln_ae` and `integral_animalLimit_eq_gamma` for `ρ = δ₁` (integrable).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNAlmostSure

open _root_.StatMech _root_.StatMech.BeffaraDC MeasureTheory

/-- The integrability hypothesis holds for the Dirac law at `1`. -/
theorem integrable_dirac_one : Integrable (id : ℝ → ℝ) (Measure.dirac 1) :=
  integrable_dirac (by simp)

/-- The animal value of the constant environment `1` at length `3` is `3`. -/
theorem animalValue_one_three : animalValue (fun _ => 1) 3 = 3 := by
  refine le_antisymm (animalValue_le_iff.mpr fun a ha => ?_) ?_
  · simpa using (Nat.cast_le.mpr ha : (a : ℝ) ≤ 3)
  · simpa using prefix_le_animalValue (ω := fun _ => (1 : ℝ)) 3 (a := 3) le_rfl

-- The shift preserves the product of `δ₁`.
example := shiftEnv_measurePreserving (Measure.dirac (1 : ℝ))

-- Almost-sure law of large numbers for `δ₁`.
example := animalValue_lln_ae integrable_dirac_one

-- The integral of the limit is the subadditive constant.
example := integral_animalLimit_eq_gamma integrable_dirac_one

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNAlmostSure
