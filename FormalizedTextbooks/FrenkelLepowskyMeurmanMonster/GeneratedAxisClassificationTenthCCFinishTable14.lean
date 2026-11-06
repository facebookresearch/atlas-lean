/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Tabulated finish boundary equations of genuine fixer 1 for columns 16 to 19;
every prefix and all sixteen signed slots are evaluated by the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 16, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_16_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 16 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 16, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_16_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 16 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 17, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_17_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 17 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 17, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_17_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 17 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 18, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_18_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 18 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 18, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_18_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 18 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 19, prefixes 0 to 127. -/
theorem generatedTenth_cc_finish_table_1_19_0 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 19 ⟨0 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every listed prefix evaluates sixteen tabulated slots and the complete final stage words.
/-- Tabulated finish equations of fixer 1, column 19, prefixes 128 to 255. -/
theorem generatedTenth_cc_finish_table_1_19_1 : ∀ u : Fin 128,
    GeneratedTenthCCBoundaryFinishTableCondition 1 19 ⟨128 + u.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryFinishTableCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
