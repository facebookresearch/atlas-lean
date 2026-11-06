/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated start boundary equations of genuine fixer 0 for prefixes 192 to 255;
all physical columns and sixteen signed slots are evaluated. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 192 to 207. -/
theorem generatedTenth_cc_start_table_0_012 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨192 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 208 to 223. -/
theorem generatedTenth_cc_start_table_0_013 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨208 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 224 to 239. -/
theorem generatedTenth_cc_start_table_0_014 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨224 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 240 to 255. -/
theorem generatedTenth_cc_start_table_0_015 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨240 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
