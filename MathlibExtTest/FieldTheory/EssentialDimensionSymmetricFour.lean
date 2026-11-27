/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.EssentialDimensionSymmetricFour

open MathlibExt.FieldTheory.EssentialDimensionSymmetric
open MathlibExt.FieldTheory.EssentialDimensionSymmetricWanted

-- The optimum is attained by a descent of transcendence degree exactly two.
example : ∃ F E : IntermediateField ℂ (rootsField 4), IsDescent 4 F E ∧ transDegNat F = 2 := by
  let degrees := {d : ℕ | ∃ F E : IntermediateField ℂ (rootsField 4),
    IsDescent 4 F E ∧ transDegNat F ≤ d}
  have hmin : sInf degrees = 2 := edSn_four_wanted
  have hne : degrees.Nonempty :=
    ⟨4, generalBaseField 4, ⊤, isDescent_generalBaseField 4, (transDegNat_generalBaseField 4).le⟩
  obtain ⟨F, E, hD, hle⟩ := Nat.sInf_mem hne
  have hge : sInf degrees ≤ transDegNat F := Nat.sInf_le ⟨F, E, hD, le_rfl⟩
  exact ⟨F, E, hD, (le_antisymm hle hge).trans hmin⟩
