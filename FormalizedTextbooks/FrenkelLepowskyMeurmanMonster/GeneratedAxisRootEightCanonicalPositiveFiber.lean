/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalCompactSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalSpatialAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! A genuine canonical fiber with the explicitly bound positive spatial transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source fiber and the positive canonical word have identical Conway classes. -/
theorem generatedRootEight_canonical_positive_spatial_projection :
    QuotientGroup.mk' signsSubgroup generatedRootEightCanonicalFiber.val.2 =
      QuotientGroup.mk' signsSubgroup generatedFifthRootEightCanonicalTransport := by
  change projH (localFiberIntoH generatedRootEightCanonicalFiber) = _
  rw [generatedRootEight_canonical_fiber_local,
    generatedFifthRootEight_canonical_local_projection]

/-- Complete Q source agreement makes the explicitly positive canonical pair compatible. -/
theorem generatedRootEight_canonical_positive_compatibility :
    spinBinaryAction (generatedRootEightCompactSpin 12) =
      leechBinaryAction generatedFifthRootEightCanonicalTransport := by
  have hb := generatedRootEight_compact_source_compatibility 12
    generatedRootEight_canonical_compact_source_condition
  rw [generatedRootEight_compact_source_canonical] at hb
  have hp := congrArg co1BinaryAction
    generatedRootEight_canonical_positive_spatial_projection
  change leechBinaryAction generatedRootEightCanonicalFiber.val.2 =
    leechBinaryAction generatedFifthRootEightCanonicalTransport at hp
  exact hb.trans hp

/-- The entire compact canonical spin paired with the genuine positive canonical isometry. -/
def generatedRootEightCanonicalPositiveFiber : localFiberSubgroup :=
  ⟨(generatedRootEightCompactSpin 12, generatedFifthRootEightCanonicalTransport),
    generatedRootEight_canonical_positive_compatibility⟩

/-- The explicitly positive canonical transport is an actual full local element. -/
def generatedRootEightCanonicalPositiveLocal : H :=
  localFiberIntoH generatedRootEightCanonicalPositiveFiber

/-- The positive canonical local element retains the exact original Conway projection. -/
theorem generatedRootEight_canonical_positive_projection :
    projH generatedRootEightCanonicalPositiveLocal =
      projH generatedFifthRootEightCanonicalLocal := by
  change QuotientGroup.mk' signsSubgroup generatedFifthRootEightCanonicalTransport = _
  exact generatedFifthRootEight_canonical_local_projection.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
