/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMask00Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite

/-! Checked literal-mask acceleration retains every original preferred-Q central phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check every6144 original binary coordinates and all256 original central coefficients.
set_option maxRecDepth 10000 in
/-- Every literal mask is the entire original input preferred-Q lift. -/
theorem generatedAxisGlobalFifthRoot00Short00InputMask_actual (i : Fin 256) :
    generatedAxisGlobalFifthPacketQFinite
          (generatedAxisGlobalFifthRoot00Short00Input i) =
      generatedAxisGlobalQMask (generatedAxisGlobalFifthRoot00Short00InputMask i) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i : Fin 256, ∀ j : Fin 24,
        toAdd (generatedAxisGlobalFifthPacketQFinite
          (generatedAxisGlobalFifthRoot00Short00Input i)).base j =
          toAdd (generatedAxisGlobalQMask
            (generatedAxisGlobalFifthRoot00Short00InputMask i)).base j := by
      decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 256,
        toAdd (generatedAxisGlobalFifthPacketQFinite
          (generatedAxisGlobalFifthRoot00Short00Input i)).coeff =
          toAdd (generatedAxisGlobalQMask
            (generatedAxisGlobalFifthRoot00Short00InputMask i)).coeff := by
      decide +kernel
    exact h i

set_option maxHeartbeats 200000000 in
-- Check every6144 original binary coordinates and all256 original central coefficients.
set_option maxRecDepth 10000 in
/-- Every literal mask is the entire original output preferred-Q lift. -/
theorem generatedAxisGlobalFifthRoot00Short00OutputMask_actual (i : Fin 256) :
    generatedAxisGlobalShortQFinite
          (generatedAxisGlobalFifthRoot00Short00Label i) =
      generatedAxisGlobalQMask (generatedAxisGlobalFifthRoot00Short00OutputMask i) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i : Fin 256, ∀ j : Fin 24,
        toAdd (generatedAxisGlobalShortQFinite
          (generatedAxisGlobalFifthRoot00Short00Label i)).base j =
          toAdd (generatedAxisGlobalQMask
            (generatedAxisGlobalFifthRoot00Short00OutputMask i)).base j := by
      decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 256,
        toAdd (generatedAxisGlobalShortQFinite
          (generatedAxisGlobalFifthRoot00Short00Label i)).coeff =
          toAdd (generatedAxisGlobalQMask
            (generatedAxisGlobalFifthRoot00Short00OutputMask i)).coeff := by
      decide +kernel
    exact h i

/-- The cached finite image inherits the already checked complete original central sign. -/
theorem generatedAxisGlobalFifthRoot00Short00_mask_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 0
      (generatedAxisGlobalQMask (generatedAxisGlobalFifthRoot00Short00InputMask i)) =
      qCentral (generatedAxisGlobalFifthRoot00Short00Phase i) *
        generatedAxisGlobalQMask (generatedAxisGlobalFifthRoot00Short00OutputMask i) := by
  have h := generatedAxisGlobalFifthRoot00Short00_QImage i
  rw [generatedAxisGlobalFifthRoot00Short00InputMask_actual,
    generatedAxisGlobalFifthRoot00Short00OutputMask_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
