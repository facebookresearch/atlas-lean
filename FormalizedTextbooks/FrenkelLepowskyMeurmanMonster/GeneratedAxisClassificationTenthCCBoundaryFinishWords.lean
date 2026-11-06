/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTableJoin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFinishTable15

/-! The complete original finish boundary words of both genuine Tenth fixers, assembled from
the certified tables and the exhaustive tabulated finish packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The tabulated finish equations hold for both fixers, all columns and all prefixes. -/
theorem generatedTenth_cc_finish_table (g : Fin 2) (j : Fin 24) (a : Fin 256) :
    GeneratedTenthCCBoundaryFinishTableCondition g j a := by
  have h : ∀ b : Fin 2, ∀ u : Fin 128,
      GeneratedTenthCCBoundaryFinishTableCondition g j ⟨128 * b.val + u.val, by omega⟩ := by
    intro b
    fin_cases g <;> fin_cases j <;> fin_cases b
    · exact generatedTenth_cc_finish_table_0_00_0
    · exact generatedTenth_cc_finish_table_0_00_1
    · exact generatedTenth_cc_finish_table_0_01_0
    · exact generatedTenth_cc_finish_table_0_01_1
    · exact generatedTenth_cc_finish_table_0_02_0
    · exact generatedTenth_cc_finish_table_0_02_1
    · exact generatedTenth_cc_finish_table_0_03_0
    · exact generatedTenth_cc_finish_table_0_03_1
    · exact generatedTenth_cc_finish_table_0_04_0
    · exact generatedTenth_cc_finish_table_0_04_1
    · exact generatedTenth_cc_finish_table_0_05_0
    · exact generatedTenth_cc_finish_table_0_05_1
    · exact generatedTenth_cc_finish_table_0_06_0
    · exact generatedTenth_cc_finish_table_0_06_1
    · exact generatedTenth_cc_finish_table_0_07_0
    · exact generatedTenth_cc_finish_table_0_07_1
    · exact generatedTenth_cc_finish_table_0_08_0
    · exact generatedTenth_cc_finish_table_0_08_1
    · exact generatedTenth_cc_finish_table_0_09_0
    · exact generatedTenth_cc_finish_table_0_09_1
    · exact generatedTenth_cc_finish_table_0_10_0
    · exact generatedTenth_cc_finish_table_0_10_1
    · exact generatedTenth_cc_finish_table_0_11_0
    · exact generatedTenth_cc_finish_table_0_11_1
    · exact generatedTenth_cc_finish_table_0_12_0
    · exact generatedTenth_cc_finish_table_0_12_1
    · exact generatedTenth_cc_finish_table_0_13_0
    · exact generatedTenth_cc_finish_table_0_13_1
    · exact generatedTenth_cc_finish_table_0_14_0
    · exact generatedTenth_cc_finish_table_0_14_1
    · exact generatedTenth_cc_finish_table_0_15_0
    · exact generatedTenth_cc_finish_table_0_15_1
    · exact generatedTenth_cc_finish_table_0_16_0
    · exact generatedTenth_cc_finish_table_0_16_1
    · exact generatedTenth_cc_finish_table_0_17_0
    · exact generatedTenth_cc_finish_table_0_17_1
    · exact generatedTenth_cc_finish_table_0_18_0
    · exact generatedTenth_cc_finish_table_0_18_1
    · exact generatedTenth_cc_finish_table_0_19_0
    · exact generatedTenth_cc_finish_table_0_19_1
    · exact generatedTenth_cc_finish_table_0_20_0
    · exact generatedTenth_cc_finish_table_0_20_1
    · exact generatedTenth_cc_finish_table_0_21_0
    · exact generatedTenth_cc_finish_table_0_21_1
    · exact generatedTenth_cc_finish_table_0_22_0
    · exact generatedTenth_cc_finish_table_0_22_1
    · exact generatedTenth_cc_finish_table_0_23_0
    · exact generatedTenth_cc_finish_table_0_23_1
    · exact generatedTenth_cc_finish_table_1_00_0
    · exact generatedTenth_cc_finish_table_1_00_1
    · exact generatedTenth_cc_finish_table_1_01_0
    · exact generatedTenth_cc_finish_table_1_01_1
    · exact generatedTenth_cc_finish_table_1_02_0
    · exact generatedTenth_cc_finish_table_1_02_1
    · exact generatedTenth_cc_finish_table_1_03_0
    · exact generatedTenth_cc_finish_table_1_03_1
    · exact generatedTenth_cc_finish_table_1_04_0
    · exact generatedTenth_cc_finish_table_1_04_1
    · exact generatedTenth_cc_finish_table_1_05_0
    · exact generatedTenth_cc_finish_table_1_05_1
    · exact generatedTenth_cc_finish_table_1_06_0
    · exact generatedTenth_cc_finish_table_1_06_1
    · exact generatedTenth_cc_finish_table_1_07_0
    · exact generatedTenth_cc_finish_table_1_07_1
    · exact generatedTenth_cc_finish_table_1_08_0
    · exact generatedTenth_cc_finish_table_1_08_1
    · exact generatedTenth_cc_finish_table_1_09_0
    · exact generatedTenth_cc_finish_table_1_09_1
    · exact generatedTenth_cc_finish_table_1_10_0
    · exact generatedTenth_cc_finish_table_1_10_1
    · exact generatedTenth_cc_finish_table_1_11_0
    · exact generatedTenth_cc_finish_table_1_11_1
    · exact generatedTenth_cc_finish_table_1_12_0
    · exact generatedTenth_cc_finish_table_1_12_1
    · exact generatedTenth_cc_finish_table_1_13_0
    · exact generatedTenth_cc_finish_table_1_13_1
    · exact generatedTenth_cc_finish_table_1_14_0
    · exact generatedTenth_cc_finish_table_1_14_1
    · exact generatedTenth_cc_finish_table_1_15_0
    · exact generatedTenth_cc_finish_table_1_15_1
    · exact generatedTenth_cc_finish_table_1_16_0
    · exact generatedTenth_cc_finish_table_1_16_1
    · exact generatedTenth_cc_finish_table_1_17_0
    · exact generatedTenth_cc_finish_table_1_17_1
    · exact generatedTenth_cc_finish_table_1_18_0
    · exact generatedTenth_cc_finish_table_1_18_1
    · exact generatedTenth_cc_finish_table_1_19_0
    · exact generatedTenth_cc_finish_table_1_19_1
    · exact generatedTenth_cc_finish_table_1_20_0
    · exact generatedTenth_cc_finish_table_1_20_1
    · exact generatedTenth_cc_finish_table_1_21_0
    · exact generatedTenth_cc_finish_table_1_21_1
    · exact generatedTenth_cc_finish_table_1_22_0
    · exact generatedTenth_cc_finish_table_1_22_1
    · exact generatedTenth_cc_finish_table_1_23_0
    · exact generatedTenth_cc_finish_table_1_23_1
  have hn := h ⟨a.val / 128, by omega⟩ ⟨a.val % 128, Nat.mod_lt _ (by decide)⟩
  have he : (⟨128 * (a.val / 128) + a.val % 128, by omega⟩ : Fin 256) = a :=
    Fin.ext (Nat.div_add_mod a.val 128)
  rw [← he]
  exact hn

/-- The complete original finish boundary words of both genuine fixers. -/
theorem generatedTenth_cc_finish_words : GeneratedTenthPackedBoundaryFinishWords := by
  intro g j a
  rw [generatedTenth_cc_post_word]
  exact generatedTenth_cc_finish_table g j a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
