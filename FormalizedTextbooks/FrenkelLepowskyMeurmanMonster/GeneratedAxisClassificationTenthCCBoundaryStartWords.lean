/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryTableJoin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCStartTable13

/-! The complete original start boundary words of both genuine Tenth fixers, assembled from
the certified tables and the exhaustive tabulated start packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The tabulated start equations hold for both fixers, all columns and all prefixes. -/
theorem generatedTenth_cc_start_table (g : Fin 2) (j : Fin 24) (a : Fin 256) :
    GeneratedTenthCCBoundaryStartTableCondition g j a := by
  have h : ∀ b : Fin 16, ∀ u : Fin 16, ∀ j : Fin 24,
      GeneratedTenthCCBoundaryStartTableCondition g j ⟨16 * b.val + u.val, by omega⟩ := by
    intro b
    fin_cases g <;> fin_cases b
    · exact generatedTenth_cc_start_table_0_000
    · exact generatedTenth_cc_start_table_0_001
    · exact generatedTenth_cc_start_table_0_002
    · exact generatedTenth_cc_start_table_0_003
    · exact generatedTenth_cc_start_table_0_004
    · exact generatedTenth_cc_start_table_0_005
    · exact generatedTenth_cc_start_table_0_006
    · exact generatedTenth_cc_start_table_0_007
    · exact generatedTenth_cc_start_table_0_008
    · exact generatedTenth_cc_start_table_0_009
    · exact generatedTenth_cc_start_table_0_010
    · exact generatedTenth_cc_start_table_0_011
    · exact generatedTenth_cc_start_table_0_012
    · exact generatedTenth_cc_start_table_0_013
    · exact generatedTenth_cc_start_table_0_014
    · exact generatedTenth_cc_start_table_0_015
    · exact generatedTenth_cc_start_table_1_000
    · exact generatedTenth_cc_start_table_1_001
    · exact generatedTenth_cc_start_table_1_002
    · exact generatedTenth_cc_start_table_1_003
    · exact generatedTenth_cc_start_table_1_004
    · exact generatedTenth_cc_start_table_1_005
    · exact generatedTenth_cc_start_table_1_006
    · exact generatedTenth_cc_start_table_1_007
    · exact generatedTenth_cc_start_table_1_008
    · exact generatedTenth_cc_start_table_1_009
    · exact generatedTenth_cc_start_table_1_010
    · exact generatedTenth_cc_start_table_1_011
    · exact generatedTenth_cc_start_table_1_012
    · exact generatedTenth_cc_start_table_1_013
    · exact generatedTenth_cc_start_table_1_014
    · exact generatedTenth_cc_start_table_1_015
  have hn := h ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩ j
  have he : (⟨16 * (a.val / 16) + a.val % 16, by omega⟩ : Fin 256) = a :=
    Fin.ext (Nat.div_add_mod a.val 16)
  rw [← he]
  exact hn

/-- The complete original start boundary words of both genuine fixers. -/
theorem generatedTenth_cc_start_words : GeneratedTenthPackedBoundaryStartWords := by
  intro g j a
  simp only [generatedTenth_cc_pre_word]
  exact generatedTenth_cc_start_table g j a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
