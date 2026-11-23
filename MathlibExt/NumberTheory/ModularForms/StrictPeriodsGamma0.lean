/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean` and
`P2M/Sol/S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Strict periods of `Γ₀(N)`

Translation by `1` is a strict period of `Γ₀(N)`, since the translation
matrix `T` lies in `Γ₀(N)`.
-/

@[expose] public section

open scoped MatrixGroups

/-- `1` is a strict period of `Γ₀(N)`: the translation matrix `T` lies in
`Γ₀(N)`, and the strict periods then contain the integer multiples of `1`. -/
theorem CongruenceSubgroup.one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have h := Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT
  rw [h]
  exact AddSubgroup.mem_zmultiples (1 : ℝ)
