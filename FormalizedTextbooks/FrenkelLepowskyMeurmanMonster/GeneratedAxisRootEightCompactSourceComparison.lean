/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQBlockTransfer

/-! Complete original and compatible compact local actions retain only an actual central sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source local element differs from the compact element by central Q alone. -/
theorem generatedRootEight_compact_source_central_difference (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) :
    localFiberIntoH (generatedRootEightCompactSourceFiber i) =
        generatedRootEightCompactSourceLocal i h ∨
      localFiberIntoH (generatedRootEightCompactSourceFiber i) =
        inclQ qCentralInvolution * generatedRootEightCompactSourceLocal i h := by
  exact generatedTwelfth_full_Q_fiber_central_difference
    (generatedRootEightCompactSourceFiber i) (generatedRootEightCompactSourceCertifiedFiber i h)
    h.symm

/-- A genuine central coefficient realizes the full original source local element. -/
theorem generatedRootEight_compact_source_central_coefficient (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) :
    ∃ c : ZMod 2, localFiberIntoH (generatedRootEightCompactSourceFiber i) =
      inclQ (qCentral c) * generatedRootEightCompactSourceLocal i h := by
  rcases generatedRootEight_compact_source_central_difference i h with he | he
  · refine ⟨0, ?_⟩
    simpa only [show qCentral 0 = (1 : Q) from rfl, map_one, one_mul] using he
  · exact ⟨1, he⟩

/-- The complete Griess source action is the compact action or its actual central transform. -/
theorem generatedRootEight_compact_source_full_action (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) (x : GriessSpace) :
    rhoLocal (localFiberIntoH (generatedRootEightCompactSourceFiber i)) x =
        rhoLocal (generatedRootEightCompactSourceLocal i h) x ∨
      rhoLocal (localFiberIntoH (generatedRootEightCompactSourceFiber i)) x =
        localCentralGriess (rhoLocal (generatedRootEightCompactSourceLocal i h) x) := by
  rcases generatedRootEight_compact_source_central_difference i h with he | he
  · exact Or.inl (congrArg (fun g : H => rhoLocal g x) he)
  · right
    rw [he, map_mul, LinearEquiv.mul_apply]
    rfl

/-- Every matrix and signed-short coordinate agrees with the actual source action. -/
theorem generatedRootEight_compact_source_matrix_short (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) (x : GriessSpace) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedRootEightCompactSourceFiber i)) x)).1 =
        (griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal i h) x)).1 ∧
    (griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedRootEightCompactSourceFiber i)) x)).2.1 =
        (griessConwayEncode (rhoLocal (generatedRootEightCompactSourceLocal i h) x)).2.1 := by
  exact generatedTwelfth_full_Q_matrix_short_blocks (generatedRootEightCompactSourceFiber i)
    (generatedRootEightCompactSourceCertifiedFiber i h) h.symm x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
