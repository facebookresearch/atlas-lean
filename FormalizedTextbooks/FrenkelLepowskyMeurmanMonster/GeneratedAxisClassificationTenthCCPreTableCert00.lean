/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Kernel certificates binding tabulated pre labels and signs of fixer 0 to the original
compact maps; every listed entry is evaluated, including all central and quadratic signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 0 to 511 of fixer 0 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_0_0 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 0 ⟨0 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 512 to 1023 of fixer 0 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_0_1 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 0 ⟨512 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 1024 to 1535 of fixer 0 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_0_2 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 0 ⟨1024 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated pre entries 1536 to 2047 of fixer 0 are the genuine values. -/
theorem generatedTenth_cc_pre_table_cert_0_3 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPreEntryCondition 0 ⟨1536 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPreEntryCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
