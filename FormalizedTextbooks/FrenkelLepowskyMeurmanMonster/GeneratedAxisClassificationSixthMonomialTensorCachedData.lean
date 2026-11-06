/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPullData

/-! Complete integer tensor checks use certified spin-label and full-phase bit-plane caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The cache preserves the full central phase, signed affine spin address and physical address. -/
def generatedSixthMonomialTensorCached (k : Fin 4) (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (generatedSixthMonomialPullPhase k n) *
    generatedSixthTensorExecutable (generatedSixthMonomialPullLabel k n)
      (generatedSixthMonomialPhysicalInput k i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
