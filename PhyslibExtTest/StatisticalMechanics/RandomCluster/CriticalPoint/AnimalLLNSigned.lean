/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNSigned

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNSigned`

With the environment law `ρ = δ₁` (every site weight equal to `1`, integrable):
* `signedAnimalValue_zero` and `signedAnimalValue_div_eq` at the constant environment;
* `signedAnimalValue_lln_ae` and `signedAnimalLimit_eq` for `ρ = δ₁`, `c = 1/2`;
* `signedAnimalValue_eventually_pos_ae` for `ρ = δ₁`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNSigned

open _root_.StatMech _root_.StatMech.BeffaraDC MeasureTheory Filter

/-- The integrability hypothesis holds for the Dirac law at `1`. -/
theorem integrable_dirac_one : Integrable (id : ℝ → ℝ) (Measure.dirac 1) :=
  integrable_dirac (by simp)

-- The signed value at length `0` vanishes.
example (c : ℝ) : signedAnimalValue (fun _ => 1) c 0 = 0 := signedAnimalValue_zero _ _

-- The signed value divided by `n` is the animal value divided by `n` minus the drift.
example :
    signedAnimalValue (fun _ => 1) (1 / 2) 3 / 3 = animalValue (fun _ => 1) 3 / 3 - 1 / 2 := by
  exact_mod_cast signedAnimalValue_div_eq (fun _ => 1) (1 / 2) (n := 3) (by norm_num)

-- The almost-sure law of large numbers for the signed value.
example := signedAnimalValue_lln_ae integrable_dirac_one (1 / 2)

-- The signed limit is the animal limit minus the drift.
example := signedAnimalLimit_eq integrable_dirac_one (1 / 2)

-- Below the animal limit the signed value is eventually positive.
example := signedAnimalValue_eventually_pos_ae integrable_dirac_one (1 / 2)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLNSigned
