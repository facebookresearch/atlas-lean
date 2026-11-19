/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model
import Mathlib.Tactic.NormNum

/-! Tests: component equations at concrete rates. -/

open Matrix

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model

open MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model

/-- Central component at rates `1, 2, 3`, evaluated directly. -/
example : (pk2Generator 1 2 3 *ᵥ ![4, 5]) 0 = 3 := by
  simp [pk2Generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Peripheral component at rates `1, 2, 3`, evaluated directly. -/
example : (pk2Generator 1 2 3 *ᵥ ![4, 5]) 1 = -7 := by
  simp [pk2Generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Zero-exchange central output, evaluated directly. -/
example : (pk2Generator 2 0 3 *ᵥ ![4, 0]) 0 = -8 := by
  simp [pk2Generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Augmented columns sum to zero at concrete rates. -/
example : ∑ i, pk2AugmentedGenerator 1 2 3 i 0 = 0 ∧
    ∑ i, pk2AugmentedGenerator 1 2 3 i 1 = 0 ∧
    ∑ i, pk2AugmentedGenerator 1 2 3 i 2 = 0 :=
  ⟨pk2_augmented_budget 1 2 3 0, pk2_augmented_budget 1 2 3 1,
    pk2_augmented_budget 1 2 3 2⟩

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model
