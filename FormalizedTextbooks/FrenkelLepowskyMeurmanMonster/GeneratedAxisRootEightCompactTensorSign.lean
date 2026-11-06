/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative

/-! Whole tensor comparisons with the final root-eight and incoming endpoints kept distinct. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The entire physical source tensor is the compact tensor with one global central sign. -/
theorem generatedRootEight_compact_source_tensor_sign (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) (x : GriessSpace) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedRootEightCompactSourceFiber i)) x)).2.2 =
        (griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal i h) x)).2.2 ∨
    (griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedRootEightCompactSourceFiber i)) x)).2.2 =
        -(griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal i h) x)).2.2 := by
  rcases generatedRootEight_compact_source_full_action i h x with he | he
  · exact Or.inl (congrArg (fun y : GriessSpace => (griessConwayEncode y).2.2) he)
  · right
    rw [he, localCentralGriess_encode]

/-- Compact index twelve compares with canonical transport of the actual final root-eight axis. -/
theorem generatedRootEight_compact_canonical_tensor_sign
    (h : generatedRootEightCompactSourceCondition 12) :
    (griessConwayEncode (rhoLocal generatedFifthRootEightCanonicalLocal
      generatedFifthRootEightAxis)).2.2 =
        (griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal 12 h)
          generatedFifthRootEightAxis)).2.2 ∨
    (griessConwayEncode (rhoLocal generatedFifthRootEightCanonicalLocal
      generatedFifthRootEightAxis)).2.2 =
        -(griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal 12 h)
          generatedFifthRootEightAxis)).2.2 := by
  have ht := generatedRootEight_compact_source_tensor_sign 12 h generatedFifthRootEightAxis
  rw [generatedRootEight_compact_source_canonical, generatedRootEight_canonical_fiber_local] at ht
  exact ht

/-- Compact index thirteen compares with the canonical incoming packet before final triality. -/
theorem generatedRootEight_compact_incoming_canonical_tensor_sign
    (h : generatedRootEightCompactSourceCondition 13) :
    (griessConwayEncode (rhoLocal generatedFifthRootEightCanonicalLocal
      (rhoLocal generatedFifthRootEightLocal generatedFifthAxis))).2.2 =
        (griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal 13 h)
          generatedFifthAxis)).2.2 ∨
    (griessConwayEncode (rhoLocal generatedFifthRootEightCanonicalLocal
      (rhoLocal generatedFifthRootEightLocal generatedFifthAxis))).2.2 =
        -(griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal 13 h)
          generatedFifthAxis)).2.2 := by
  have ht := generatedRootEight_compact_source_tensor_sign 13 h generatedFifthAxis
  rw [generatedRootEight_compact_source_incoming, map_mul,
    generatedRootEight_canonical_fiber_local, generatedTenth_Q_word_fiber_local,
    map_mul, LinearEquiv.mul_apply] at ht
  exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
