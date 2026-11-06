/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountGolayData

/-! Final finite convolutions and the Golay label sum.
These numerical statements count the preceding certified source histograms;
their interpretation as lattice-vector cardinalities is proved separately. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Five code weights and two parities each require a bounded520-term convolution.
/-- The bounded histograms give these exact product coefficients at norm64. -/
theorem leechNormEightCountTable_product : ∀ m : Bool, ∀ k : Fin 5,
    (∑ q : Fin 65, ∑ r : ZMod 8,
      leechNormEightCountTable m 0
        ⟨24 - (leechNormEightGolayWeights k).val, by omega⟩ q r *
      leechNormEightCountTable m 1 (leechNormEightGolayWeights k)
        ⟨64 - q.val, by omega⟩ (4 * (m.toNat : ZMod 8) - r)) =
      leechNormEightWordContribution m (leechNormEightGolayWeights k).val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
