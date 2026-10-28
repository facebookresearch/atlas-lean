/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated start boundary equations of genuine fixer 1 for prefixes 64 to 127;
all physical columns and sixteen signed slots are evaluated. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 1, all columns, prefixes 64 to 79. -/
theorem generatedTenth_cc_start_table_1_004 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 1 j ⟨64 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 1, all columns, prefixes 80 to 95. -/
theorem generatedTenth_cc_start_table_1_005 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 1 j ⟨80 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 1, all columns, prefixes 96 to 111. -/
theorem generatedTenth_cc_start_table_1_006 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 1 j ⟨96 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 1, all columns, prefixes 112 to 127. -/
theorem generatedTenth_cc_start_table_1_007 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 1 j ⟨112 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
