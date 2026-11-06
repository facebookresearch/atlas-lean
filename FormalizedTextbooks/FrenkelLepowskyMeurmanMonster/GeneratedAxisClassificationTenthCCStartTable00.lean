/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated start boundary equations of genuine fixer 0 for prefixes 0 to 63;
all physical columns and sixteen signed slots are evaluated. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 0 to 15. -/
theorem generatedTenth_cc_start_table_0_000 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 16 to 31. -/
theorem generatedTenth_cc_start_table_0_001 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨16 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 32 to 47. -/
theorem generatedTenth_cc_start_table_0_002 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨32 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 48 to 63. -/
theorem generatedTenth_cc_start_table_0_003 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨48 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
