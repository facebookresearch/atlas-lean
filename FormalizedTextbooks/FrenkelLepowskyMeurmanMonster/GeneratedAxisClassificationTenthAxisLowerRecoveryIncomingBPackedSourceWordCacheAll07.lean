/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0700
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0701
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0702
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0703

/-! All 256 original packed words in one complete signed physical source column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original source-word equality includes all sixteen original slots. -/
theorem generatedTenth_incoming_B_source_word_cache_all_07 (a : Fin 256) :
    generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache
      ⟨7, by omega⟩ a = generatedTenthIncomingBSourceWordCache07 a := by
  apply generatedTenth_incoming_B_source_word_cache_of_four
    (fun a => generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache
      ⟨7, by omega⟩ a = generatedTenthIncomingBSourceWordCache07 a)
  intro b u
  fin_cases b
  · exact generatedTenth_incoming_B_source_word_cache_certificate_07_00 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_07_01 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_07_02 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_07_03 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
