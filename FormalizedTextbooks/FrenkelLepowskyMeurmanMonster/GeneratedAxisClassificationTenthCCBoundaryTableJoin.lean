/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPostTableCert00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPostTableCert01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPostTableCert10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPostTableCert11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPreTableCert00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPreTableCert01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPreTableCert10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCPreTableCert11

/-! All tabulated pre and post entries are genuine, so the original boundary words of both
fixers equal their tabulated forms; every label and sign is kernel certified. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every tabulated post entry of both fixers is the genuine label and sign. -/
theorem generatedTenth_cc_post_entries (g : Fin 2) (n : Fin 4096) :
    GeneratedTenthCCBoundaryPostEntryCondition g n := by
  have h : ∀ b : Fin 8, ∀ v : Fin 512,
      GeneratedTenthCCBoundaryPostEntryCondition g ⟨512 * b.val + v.val, by omega⟩ := by
    intro b
    fin_cases g <;> fin_cases b
    · exact generatedTenth_cc_post_table_cert_0_0
    · exact generatedTenth_cc_post_table_cert_0_1
    · exact generatedTenth_cc_post_table_cert_0_2
    · exact generatedTenth_cc_post_table_cert_0_3
    · exact generatedTenth_cc_post_table_cert_0_4
    · exact generatedTenth_cc_post_table_cert_0_5
    · exact generatedTenth_cc_post_table_cert_0_6
    · exact generatedTenth_cc_post_table_cert_0_7
    · exact generatedTenth_cc_post_table_cert_1_0
    · exact generatedTenth_cc_post_table_cert_1_1
    · exact generatedTenth_cc_post_table_cert_1_2
    · exact generatedTenth_cc_post_table_cert_1_3
    · exact generatedTenth_cc_post_table_cert_1_4
    · exact generatedTenth_cc_post_table_cert_1_5
    · exact generatedTenth_cc_post_table_cert_1_6
    · exact generatedTenth_cc_post_table_cert_1_7
  have hn := h ⟨n.val / 512, by omega⟩ ⟨n.val % 512, Nat.mod_lt _ (by decide)⟩
  have he : (⟨512 * (n.val / 512) + n.val % 512, by omega⟩ : Fin 4096) = n :=
    Fin.ext (Nat.div_add_mod n.val 512)
  rw [← he]
  exact hn

/-- Every tabulated pre entry of both fixers is the genuine label and sign. -/
theorem generatedTenth_cc_pre_entries (g : Fin 2) (n : Fin 4096) :
    GeneratedTenthCCBoundaryPreEntryCondition g n := by
  have h : ∀ b : Fin 8, ∀ v : Fin 512,
      GeneratedTenthCCBoundaryPreEntryCondition g ⟨512 * b.val + v.val, by omega⟩ := by
    intro b
    fin_cases g <;> fin_cases b
    · exact generatedTenth_cc_pre_table_cert_0_0
    · exact generatedTenth_cc_pre_table_cert_0_1
    · exact generatedTenth_cc_pre_table_cert_0_2
    · exact generatedTenth_cc_pre_table_cert_0_3
    · exact generatedTenth_cc_pre_table_cert_0_4
    · exact generatedTenth_cc_pre_table_cert_0_5
    · exact generatedTenth_cc_pre_table_cert_0_6
    · exact generatedTenth_cc_pre_table_cert_0_7
    · exact generatedTenth_cc_pre_table_cert_1_0
    · exact generatedTenth_cc_pre_table_cert_1_1
    · exact generatedTenth_cc_pre_table_cert_1_2
    · exact generatedTenth_cc_pre_table_cert_1_3
    · exact generatedTenth_cc_pre_table_cert_1_4
    · exact generatedTenth_cc_pre_table_cert_1_5
    · exact generatedTenth_cc_pre_table_cert_1_6
    · exact generatedTenth_cc_pre_table_cert_1_7
  have hn := h ⟨n.val / 512, by omega⟩ ⟨n.val % 512, Nat.mod_lt _ (by decide)⟩
  have he : (⟨512 * (n.val / 512) + n.val % 512, by omega⟩ : Fin 4096) = n :=
    Fin.ext (Nat.div_add_mod n.val 512)
  rw [← he]
  exact hn

/-- The genuine post integer is the tabulated sign times the tabulated permuted coordinate. -/
theorem generatedTenth_cc_post_integer (g : Fin 2) (v : NortonUIntegerVector) (n : Fin 4096) :
    generatedTenthTwoFixerTensorPostInteger g v n =
      generatedTenthCCBoundaryPostSign g n * v (generatedTenthCCBoundaryPostLabel g n) := by
  obtain ⟨h1, h2⟩ := generatedTenth_cc_post_entries g n
  change generatedAxisGlobalIntSign (spinPhase (generatedTenthTwoFixerTensorPauli g)
      (golayLabelCoefficients n)) *
    generatedAxisGlobalIntSign (monsterMonomialQuadratic
      (generatedTenthTwoFixerTensorFirstPhase g) ((generatedTenthTwoFixerTensorLeft g).symm
        (golayLabelCoefficients n + spinTranslation (generatedTenthTwoFixerTensorPauli g)))) *
    v (nortonUIntegerLabel ((generatedTenthTwoFixerTensorLeft g).symm
      (golayLabelCoefficients n + spinTranslation (generatedTenthTwoFixerTensorPauli g)))) = _
  rw [h1, h2]

/-- The genuine pre integer is the tabulated sign times the tabulated permuted coordinate. -/
theorem generatedTenth_cc_pre_integer (g : Fin 2) (v : NortonUIntegerVector) (n : Fin 4096) :
    generatedTenthTwoFixerTensorPreInteger g v n =
      generatedTenthCCBoundaryPreSign g n * v (generatedTenthCCBoundaryPreLabel g n) := by
  obtain ⟨h1, h2⟩ := generatedTenth_cc_pre_entries g n
  unfold generatedTenthTwoFixerTensorPreInteger
  rw [h1, h2]

/-- The genuine post word equals its tabulated form at every prefix. -/
theorem generatedTenth_cc_post_word (g : Fin 2) (j : Fin 24) (a : Fin 256) :
    generatedTenthPackedBoundaryPostWord g j a = generatedTenthCCBoundaryPostTableWord g j a := by
  unfold generatedTenthPackedBoundaryPostWord generatedTenthCCBoundaryPostTableWord
  exact congrArg generatedTenthPackedBoundaryWord
    (funext fun i => generatedTenth_cc_post_integer g _ _)

/-- The genuine pre word equals its tabulated form at every prefix. -/
theorem generatedTenth_cc_pre_word (g : Fin 2) (k : Fin 24) (a : Fin 256) :
    generatedTenthPackedBoundaryPreWord g k a = generatedTenthCCBoundaryPreTableWord g k a := by
  unfold generatedTenthPackedBoundaryPreWord generatedTenthCCBoundaryPreTableWord
  exact congrArg generatedTenthPackedBoundaryWord
    (funext fun i => generatedTenth_cc_pre_integer g _ _)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
