/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated finish boundary equations of genuine fixer 1 for columns 12 to 15;
every prefix and all sixteen signed slots are evaluated by the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 12, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_12_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 12 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 12, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_12_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 12 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 13, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_13_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 13 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 13, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_13_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 13 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 14, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_14_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 14 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 14, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_14_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 14 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 15, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_15_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 15 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 15, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_15_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 15 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
