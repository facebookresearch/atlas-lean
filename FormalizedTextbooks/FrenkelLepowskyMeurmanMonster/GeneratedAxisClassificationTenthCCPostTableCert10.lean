/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTables

/-! Kernel certificates binding tabulated post labels and signs of fixer 1 to the original
compact maps; every listed entry is evaluated, including all central and quadratic signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated post entries 0 to 511 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_post_table_cert_1_0 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPostEntryCondition 1 ⟨0 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPostEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated post entries 512 to 1023 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_post_table_cert_1_1 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPostEntryCondition 1 ⟨512 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPostEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated post entries 1024 to 1535 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_post_table_cert_1_2 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPostEntryCondition 1 ⟨1024 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPostEntryCondition
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Every one of these 512 entries evaluates the genuine label map and its full sign.
/-- Tabulated post entries 1536 to 2047 of fixer 1 are the genuine values. -/
theorem generatedTenth_cc_post_table_cert_1_3 : ∀ v : Fin 512,
    GeneratedTenthCCBoundaryPostEntryCondition 1 ⟨1536 + v.val, by omega⟩ := by
  unfold GeneratedTenthCCBoundaryPostEntryCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
