/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort06Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite

/-! Full kernel-checked preferred-Q transport for root-zero packet batch 6. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check all6144 actual binary coordinates and all256 genuine central phases in this batch.
set_option maxRecDepth 10000 in
/-- Every candidate row is the entire genuine preferred-Q image, including its central sign. -/
theorem generatedAxisGlobalFifthRoot00Short06_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 0
      (generatedAxisGlobalFifthPacketQFinite (generatedAxisGlobalFifthRoot00Short06Input i)) =
      qCentral (generatedAxisGlobalFifthRoot00Short06Phase i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot00Short06Label i) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i : Fin 256, ∀ j : Fin 24,
        toAdd (generatedAxisGlobalFifthQFast 0
          (generatedAxisGlobalFifthPacketQFinite
            (generatedAxisGlobalFifthRoot00Short06Input i))).base j =
        toAdd (qCentral (generatedAxisGlobalFifthRoot00Short06Phase i) *
          generatedAxisGlobalShortQFinite
            (generatedAxisGlobalFifthRoot00Short06Label i)).base j := by
      decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 256,
        toAdd (generatedAxisGlobalFifthQFast 0
          (generatedAxisGlobalFifthPacketQFinite
            (generatedAxisGlobalFifthRoot00Short06Input i))).coeff =
        toAdd (qCentral (generatedAxisGlobalFifthRoot00Short06Phase i) *
          generatedAxisGlobalShortQFinite
            (generatedAxisGlobalFifthRoot00Short06Label i)).coeff := by
      decide +kernel
    exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
