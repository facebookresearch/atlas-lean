/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Kernel certificates binding tabulated pre labels and signs of fixer 1 to the original
compact maps; every listed entry is evaluated, including all central and quadratic signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 2048 to 2559 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_1_4 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 1 ⟨2048 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 2560 to 3071 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_1_5 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 1 ⟨2560 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 3072 to 3583 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_1_6 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 1 ⟨3072 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 3584 to 4095 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_1_7 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 1 ⟨3584 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
