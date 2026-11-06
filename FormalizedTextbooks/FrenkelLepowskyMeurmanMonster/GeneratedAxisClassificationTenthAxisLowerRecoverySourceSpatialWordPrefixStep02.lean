/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixGeneric

/-! Ungated exact source prefixes; all finite and symbolic proofs are drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Scope one full576-entry single-stage product, with only24 terms per entry.
/-- Closed literal next-prefix certificate, with no nested original word products. -/
theorem generatedTenth_source_spatial_word_prefix_step_02 :
    GeneratedTenthSourceSpatialWordPrefixStep 2 := by
  unfold GeneratedTenthSourceSpatialWordPrefixStep
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
