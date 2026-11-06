/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCacheData

/-! Entire genuine coordinate images of odd-family original root word 3. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 80000000 in
-- Check24 complete original word images using only previously verified finite letter caches.
/-- Every cached root coordinate lift equals the full compact original source product image. -/
theorem generatedAxisGlobalOddRootQCache03_certificate (i : Fin 24) :
    generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords 3)
        (qCoordinateGenerator i) = generatedAxisGlobalOddRootQCache 3 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24,
        toAdd (generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords 3)
          (qCoordinateGenerator i)).base j =
            toAdd (generatedAxisGlobalOddRootQCache 3 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24,
        toAdd (generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords 3)
          (qCoordinateGenerator i)).coeff =
            toAdd (generatedAxisGlobalOddRootQCache 3 i).coeff := by decide +kernel
    exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
