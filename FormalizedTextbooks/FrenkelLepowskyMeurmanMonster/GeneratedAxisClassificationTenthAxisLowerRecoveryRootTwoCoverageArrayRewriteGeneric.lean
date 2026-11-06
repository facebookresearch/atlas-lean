/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoRowDescriptorIndexCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoDictionaryWordIndexCache

/-! Exact original indexed row and dictionary access for complete coverage certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Balanced row lookup is the complete original descriptor, with every packed bit retained. -/
theorem generatedTenth_root_two_coverage_row_descriptor_cached_actual (k : Fin 4136) :
    generatedTenthRootTwoRowDescriptorIndexTree.lookup k.val =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowDescriptor k := by
  unfold generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowDescriptor
  exact generatedTenth_root_two_row_descriptor_index_tree_actual k.val

/-- Balanced dictionary lookup retains the original key, row, numerator and zero default. -/
theorem generatedTenth_root_two_coverage_dictionary_word_cached_actual (a : Fin 3856) :
    generatedTenthRootTwoDictionaryWordIndexTree.lookup a.val =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryWord a := by
  unfold generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryWord
  exact generatedTenth_root_two_dictionary_word_index_tree_actual a.val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
