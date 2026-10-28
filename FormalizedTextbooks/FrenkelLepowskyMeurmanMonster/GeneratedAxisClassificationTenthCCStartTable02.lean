/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated start boundary equations of genuine fixer 0 for prefixes 128 to 191;
all physical columns and sixteen signed slots are evaluated. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 128 to 143. -/
theorem generatedTenth_cc_start_table_0_008 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 144 to 159. -/
theorem generatedTenth_cc_start_table_0_009 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨144 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 160 to 175. -/
theorem generatedTenth_cc_start_table_0_010 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨160 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Each prefix evaluates all twenty-four tabulated pre words once for every physical column.
/-- Tabulated start equations of fixer 0, all columns, prefixes 176 to 191. -/
theorem generatedTenth_cc_start_table_0_011 : ∀ u : Fin 16, ∀ j : Fin 24,
    GeneratedTenthCCBoundaryStartTableCondition 0 j ⟨176 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryStartTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
