/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorInteger

/-! The complete source odd-axis starting packet is the original two-point rank-one tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Check every physical spin coordinate, including all 4094 original zero entries.
/-- The mask packet is exactly the original two-point signed Hadamard vector. -/
theorem generatedAxisGlobalOddRoot00Spin00_original (k : Fin 4096) :
    generatedAxisGlobalOddRoot00Spin00 k =
      -8 * generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
        (if k.val % 2048 = 0 then 1 else 0) := by
  have h : ∀ k : Fin 4096, generatedAxisGlobalOddRoot00Spin00 k =
      -8 * generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
        (if k.val % 2048 = 0 then 1 else 0) := by decide +kernel
  exact h k

/-- Both independent original source words start with precisely the same spin vector. -/
theorem generatedAxisGlobalOddRoot06Spin00_eq :
    generatedAxisGlobalOddRoot06Spin00 = generatedAxisGlobalOddRoot00Spin00 := rfl

/-- The starting physical spatial numerator is the original coordinate zero. -/
theorem generatedAxisGlobalOddRoot00Spatial00_original :
    generatedAxisGlobalOddRoot00Spatial00 = (Pi.single 0 1 : Fin 24 → ℤ) := by
  have h : ∀ i : Fin 24,
      generatedAxisGlobalOddRoot00Spatial00 i = (Pi.single 0 1 : Fin 24 → ℤ) i := by
    decide +kernel
  exact funext h

/-- The second word has the identical original physical coordinate-zero spatial factor. -/
theorem generatedAxisGlobalOddRoot06Spatial00_eq :
    generatedAxisGlobalOddRoot06Spatial00 = generatedAxisGlobalOddRoot00Spatial00 := rfl

/-- The entire complete original integer tensor is the stated two physical factors. -/
theorem generatedAxisGlobalOddRoot00InitialFactor :
    generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin00
      generatedAxisGlobalOddRoot00Spatial00 = generatedAxisGlobalOddTensorInteger := by
  funext k i
  have hd : (spinDictionaryCode (golayLabelCoefficients k) = 0) ↔ k.val % 2048 = 0 := by
    rw [← generatedAxisGlobalSpinLabelLow_dictionary]
    simp only [Fin.ext_iff, generatedAxisGlobalSpinLabelLow, Fin.val_zero]
  rw [generatedAxisGlobalOddTensorFactor, generatedAxisGlobalOddRoot00Spin00_original,
    generatedAxisGlobalOddRoot00Spatial00_original]
  simp only [generatedAxisGlobalOddTensorInteger, hd, Pi.single_apply]

/-- The complete second starting packet is the same original actual tensor. -/
theorem generatedAxisGlobalOddRoot06InitialFactor :
    generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin00
      generatedAxisGlobalOddRoot06Spatial00 = generatedAxisGlobalOddTensorInteger := by
  rw [generatedAxisGlobalOddRoot06Spin00_eq, generatedAxisGlobalOddRoot06Spatial00_eq]
  exact generatedAxisGlobalOddRoot00InitialFactor

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
