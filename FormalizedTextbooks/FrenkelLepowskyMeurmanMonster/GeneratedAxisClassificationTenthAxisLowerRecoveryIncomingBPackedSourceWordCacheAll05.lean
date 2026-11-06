/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0500
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0501
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0502
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheCertificate0503

/-! All 256 original packed words in one complete signed physical source column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original source-word equality includes all sixteen original slots. -/
theorem generatedTenth_incoming_B_source_word_cache_all_05 (a : Fin 256) :
    generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache
      ⟨5, by omega⟩ a = generatedTenthIncomingBSourceWordCache05 a := by
  apply generatedTenth_incoming_B_source_word_cache_of_four
    (fun a => generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache
      ⟨5, by omega⟩ a = generatedTenthIncomingBSourceWordCache05 a)
  intro b u
  fin_cases b
  · exact generatedTenth_incoming_B_source_word_cache_certificate_05_00 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_05_01 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_05_02 u
  · exact generatedTenth_incoming_B_source_word_cache_certificate_05_03 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
