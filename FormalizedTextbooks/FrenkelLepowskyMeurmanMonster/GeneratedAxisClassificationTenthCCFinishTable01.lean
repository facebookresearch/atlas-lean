/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated finish boundary equations of genuine fixer 0 for columns 4 to 7;
every prefix and all sixteen signed slots are evaluated by the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 4, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_0_04_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 4 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 4, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_0_04_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 4 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 5, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_0_05_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 5 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 5, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_0_05_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 5 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 6, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_0_06_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 6 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 6, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_0_06_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 6 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 7, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_0_07_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 7 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 0, column 7, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_0_07_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 0 7 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
