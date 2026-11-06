/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixMetadata00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixMetadata01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixMetadata02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixMetadata03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixMetadata04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixMetadata05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixMetadata06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixStep00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixStep01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixStep02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixStep03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixStep04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixStep05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixStep06

/-! Ungated exact source prefixes; all finite and symbolic proofs are drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every actual source stage retains its complete original metadata. -/
theorem generatedTenth_source_spatial_word_prefix_all_metadata (j : Fin 7) :
    GeneratedTenthSourceSpatialWordPrefixMetadata j := by
  fin_cases j
  · exact generatedTenth_source_spatial_word_prefix_metadata_00
  · exact generatedTenth_source_spatial_word_prefix_metadata_01
  · exact generatedTenth_source_spatial_word_prefix_metadata_02
  · exact generatedTenth_source_spatial_word_prefix_metadata_03
  · exact generatedTenth_source_spatial_word_prefix_metadata_04
  · exact generatedTenth_source_spatial_word_prefix_metadata_05
  · exact generatedTenth_source_spatial_word_prefix_metadata_06

/-- The seven independent next-prefix certificates cover the complete physical word. -/
theorem generatedTenth_source_spatial_word_prefix_all_steps (j : Fin 7) :
    GeneratedTenthSourceSpatialWordPrefixStep j := by
  fin_cases j
  · exact generatedTenth_source_spatial_word_prefix_step_00
  · exact generatedTenth_source_spatial_word_prefix_step_01
  · exact generatedTenth_source_spatial_word_prefix_step_02
  · exact generatedTenth_source_spatial_word_prefix_step_03
  · exact generatedTenth_source_spatial_word_prefix_step_04
  · exact generatedTenth_source_spatial_word_prefix_step_05
  · exact generatedTenth_source_spatial_word_prefix_step_06

/-- Complete actual physical P equality via seven symbolic steps, not a seven-product decision. -/
theorem generatedTenth_source_spatial_word_prefix_eq :
    generatedTenthSourceSpatialWordLiteral = generatedAxisGlobalFifthSpatialWordMatrix 2 :=
  (generatedTenth_source_spatial_word_prefix_word
    generatedTenth_source_spatial_word_prefix_all_metadata
    generatedTenth_source_spatial_word_prefix_all_steps).symm

/-- Same whole576-entry source statement as the held literal certificate, new proof route. -/
theorem generatedTenth_source_spatial_word_prefix_certificate :
    ∀ i j : Fin 24,
      generatedTenthSourceSpatialWordLiteral i j =
        generatedAxisGlobalFifthSpatialWordMatrix 2 i j := by
  intro i j
  rw [generatedTenth_source_spatial_word_prefix_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
