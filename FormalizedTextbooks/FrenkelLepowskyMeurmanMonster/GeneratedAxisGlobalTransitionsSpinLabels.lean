/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairTensor

/-! Executable labels for the actual physical spin coordinate basis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The binary weight of an actual physical spin coordinate vector. -/
def generatedAxisGlobalSpinLabelValue (t : SpinIndex) : ℕ :=
  ∑ j : Fin 12, (t j).val * 2 ^ j.val

/-- Every actual spin coordinate vector has a genuine twelve-bit bounded label. -/
theorem generatedAxisGlobalSpinLabelValue_bound (t : SpinIndex) :
    generatedAxisGlobalSpinLabelValue t < 4096 := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  change (∑ j : Fin 12, (golayLabelCoefficients k j).val * 2 ^ j.val) < 4096
  rw [golayLabelCoefficients_reassemble]
  exact k.isLt

/-- A computable source-coordinate label, defined by bit weights in the actual spin space. -/
def generatedAxisGlobalSpinLabel (t : SpinIndex) : Fin 4096 :=
  ⟨generatedAxisGlobalSpinLabelValue t, generatedAxisGlobalSpinLabelValue_bound t⟩

/-- Encoding a displayed physical row recovers exactly its original source label. -/
theorem generatedAxisGlobalSpinLabel_coeff (k : Fin 4096) :
    generatedAxisGlobalSpinLabel (golayLabelCoefficients k) = k := by
  apply Fin.ext
  exact golayLabelCoefficients_reassemble k

/-- Decoding the computable label recovers the original actual physical spin row. -/
theorem generatedAxisGlobalSpinLabel_decode (t : SpinIndex) :
    golayLabelCoefficients (generatedAxisGlobalSpinLabel t) = t := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  rw [generatedAxisGlobalSpinLabel_coeff]

/-- The finite executable label agrees with the actual physical dictionary label. -/
theorem generatedAxisGlobalSpinLabel_eq_dictionary (t : SpinIndex) :
    generatedAxisGlobalSpinLabel t = spinDictionaryLabel t := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  rw [generatedAxisGlobalSpinLabel_coeff, spinDictionaryLabel_coeff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
