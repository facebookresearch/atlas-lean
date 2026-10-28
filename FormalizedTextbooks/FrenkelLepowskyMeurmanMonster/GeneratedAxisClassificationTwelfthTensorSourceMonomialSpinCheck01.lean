/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceIntermediateSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheSoundness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
/-- The whole compact source word has the certified value at every spin coordinate. -/
theorem generatedTwelfth_tensor_source_monomial_spin_check01 : ∀ (r : Fin 8) (a : Fin 4096),
    generatedTwelfthTensorSourceMonomialPhaseSign 1 a *
        generatedTwelfthTensorSourceSpinNumerator 1 r
          (generatedTwelfthTensorSourceMonomialPull 1 a) =
      generatedTwelfthTensorSourceIntermediateSpin 2 r a := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
