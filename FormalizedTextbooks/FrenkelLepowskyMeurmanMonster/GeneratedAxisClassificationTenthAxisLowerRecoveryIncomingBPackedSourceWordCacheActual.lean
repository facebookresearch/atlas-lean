/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheAll07

/-! Whole original source-word and genuine signed source-slot bindings. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All eight original physical columns retain their 256 complete sixteen-slot words. -/
def generatedTenthIncomingBSourceWordCache : Fin 8 → Fin 256 → ℕ :=
  ![generatedTenthIncomingBSourceWordCache00,
    generatedTenthIncomingBSourceWordCache01,
    generatedTenthIncomingBSourceWordCache02,
    generatedTenthIncomingBSourceWordCache03,
    generatedTenthIncomingBSourceWordCache04,
    generatedTenthIncomingBSourceWordCache05,
    generatedTenthIncomingBSourceWordCache06,
    generatedTenthIncomingBSourceWordCache07]

/-- The cached word is exactly the original packed source word at every column and prefix. -/
theorem generatedTenth_incoming_B_source_word_cache_actual (r : Fin 8) (a : Fin 256) :
    generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache r a =
      generatedTenthIncomingBSourceWordCache r a := by
  fin_cases r
  · exact generatedTenth_incoming_B_source_word_cache_all_00 a
  · exact generatedTenth_incoming_B_source_word_cache_all_01 a
  · exact generatedTenth_incoming_B_source_word_cache_all_02 a
  · exact generatedTenth_incoming_B_source_word_cache_all_03 a
  · exact generatedTenth_incoming_B_source_word_cache_all_04 a
  · exact generatedTenth_incoming_B_source_word_cache_all_05 a
  · exact generatedTenth_incoming_B_source_word_cache_all_06 a
  · exact generatedTenth_incoming_B_source_word_cache_all_07 a

/-- A whole function equality permits consumer proof rewrites without changing old predicates. -/
theorem generatedTenth_incoming_B_source_word_cache_function :
    generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache =
      generatedTenthIncomingBSourceWordCache := by
  funext r a
  exact generatedTenth_incoming_B_source_word_cache_actual r a

/-- Every cached digit is the complete actual paired source sum with its original full phases. -/
theorem generatedTenth_incoming_B_source_word_cache_digit
    (r : Fin 8) (a : Fin 256) (s : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthIncomingBSourceWordCache r a) s =
      generatedTenthSourceColumnSpinSum r (generatedNinthLowerSpinPackedPrefixIndex a s) := by
  rw [← generatedTenth_incoming_B_source_word_cache_actual]
  exact generatedTenth_incoming_B_packed_actual_source_digit r a s

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
