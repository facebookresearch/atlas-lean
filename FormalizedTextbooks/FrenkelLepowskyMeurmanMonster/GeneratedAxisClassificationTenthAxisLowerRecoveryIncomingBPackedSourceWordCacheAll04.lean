/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0400
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0401
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0402
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0403

/-! All 256 original packed words in one complete signed physical source column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original source-word equality includes all sixteen original slots. -/
theorem generatedTenth_incoming_B_source_word_cache_all_04 (a : Fin 256) :
    generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache
      ⟨4, by omega⟩ a = generatedTenthIncomingBSourceWordCache04 a := by
  apply generatedTenth_incoming_B_source_word_cache_of_four
    (fun a => generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache
      ⟨4, by omega⟩ a = generatedTenthIncomingBSourceWordCache04 a)
  intro b u
  fin_cases b
  · exact generatedTenth_incoming_B_source_word_cache_certificate_04_00 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_04_01 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_04_02 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_04_03 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
