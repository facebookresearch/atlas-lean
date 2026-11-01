/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated finish boundary equations of genuine fixer 1 for columns 0 to 3;
every prefix and all sixteen signed slots are evaluated by the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 0, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_00_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 0 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 0, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_00_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 0 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 1, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_01_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 1 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 1, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_01_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 1 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 2, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_02_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 2 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 2, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_02_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 2 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 3, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_03_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 3 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 3, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_03_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 3 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
