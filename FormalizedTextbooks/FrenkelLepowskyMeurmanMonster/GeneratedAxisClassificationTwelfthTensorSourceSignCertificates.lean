/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheCheck02

/-! Complete actual source-operator consequences of the bounded original certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every complete high-bit source sign is its certified genuine four-input formula. -/
theorem generatedTwelfth_tensor_source_sign_cached_actual (j : Fin 3) (u : Fin 4096 → ℤ) :
    generatedTwelfthTensorSignSpinInteger (generatedTwelfthTensorSourceSignCode j) u =
      generatedTwelfthTensorSourceSignSpinCompact j u := by
  apply generatedTwelfth_tensor_source_sign_spin_compact
  intro e
  fin_cases j
  · exact generatedTwelfth_tensor_source_sign_cache_check00 e
  · exact generatedTwelfth_tensor_source_sign_cache_check01 e
  · exact generatedTwelfth_tensor_source_sign_cache_check02 e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
