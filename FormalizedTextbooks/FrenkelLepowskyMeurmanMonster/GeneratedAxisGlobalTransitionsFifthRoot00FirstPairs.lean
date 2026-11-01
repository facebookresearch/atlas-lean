/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairQFinite
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortFastPacket

/-! First complete actual signed-short images of the genuine fifth root-zero normalization word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Four original pair indices representing coordinates(0,4),(0,5),(0,6),(0,7). -/
def generatedAxisGlobalFifthRoot00FirstPairIndex (i : Fin 4) : Fin 276 :=
  ⟨3 + i.val, by omega⟩

/-- Candidate outgoing original odd-family code labels. -/
def generatedAxisGlobalFifthRoot00FirstPairOddCode : Fin 2 → Fin 4 → Fin 2048 :=
  ![![836, 846, 841, 839], ![832, 842, 845, 835]]

/-- The actual odd-family coordinate described by each outgoing original code label. -/
def generatedAxisGlobalFifthRoot00FirstPairOddLabel (s : Fin 2) (i : Fin 4) : GriessShortIndex :=
  Sum.inr (Sum.inr (generatedAxisGlobalFifthRoot00FirstPairOddCode s i, 0))

/-- Candidate full central phases of these genuine preferred-Q images. -/
def generatedAxisGlobalFifthRoot00FirstPairPhase : Fin 2 → Fin 4 → ZMod 2 :=
  ![![0, 0, 0, 1], ![1, 1, 1, 0]]

set_option maxHeartbeats 20000000 in
-- Check all192 scalar binary coordinates and all eight genuine central signs.
set_option maxRecDepth 10000 in
/-- The checked complete preferred-Q image of each of the eight original pair lifts. -/
theorem generatedAxisGlobalFifthRoot00FirstPair_QImage (s : Fin 2) (i : Fin 4) :
    generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalPairQFinite s
      (generatedAxisGlobalFifthRoot00FirstPairIndex i)) =
        qCentral (generatedAxisGlobalFifthRoot00FirstPairPhase s i) *
          monsterNortonShortQSource
            (generatedAxisGlobalFifthRoot00FirstPairOddLabel s i) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ s : Fin 2, ∀ i : Fin 4, ∀ j : Fin 24,
        toAdd (generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalPairQFinite s
          (generatedAxisGlobalFifthRoot00FirstPairIndex i))).base j =
            toAdd (qCentral (generatedAxisGlobalFifthRoot00FirstPairPhase s i) *
              monsterNortonShortQSource
                (generatedAxisGlobalFifthRoot00FirstPairOddLabel s i)).base j := by
      decide +kernel
    exact h s i j
  · apply toAdd.injective
    have h : ∀ s : Fin 2, ∀ i : Fin 4,
        toAdd (generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalPairQFinite s
          (generatedAxisGlobalFifthRoot00FirstPairIndex i))).coeff =
            toAdd (qCentral (generatedAxisGlobalFifthRoot00FirstPairPhase s i) *
              monsterNortonShortQSource
                (generatedAxisGlobalFifthRoot00FirstPairOddLabel s i)).coeff := by
      decide +kernel
    exact h s i

/-- These eight finite Q certificates give entire actual signed Griess-unit transports. -/
theorem generatedAxisGlobalFifthRoot00FirstPair_griess (s : Fin 2) (i : Fin 4) :
    rhoLocal (generatedAxisGlobalFifthShortLocalWord 0)
        (griessConwayDecode (0, (Pi.single
          (Sum.inl (s, generatedAxisGlobalFifthRoot00FirstPairIndex i)) (1 : ℝ), 0))) =
      griessConwayDecode (0, (qSign (generatedAxisGlobalFifthRoot00FirstPairPhase s i) •
        Pi.single (generatedAxisGlobalFifthRoot00FirstPairOddLabel s i)
          (1 : ℝ), 0)) := by
  apply generatedAxisGlobalFifthQFast_griess_basis 0 generatedAxisGlobalFifthQCache00_actual
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, ← generatedAxisGlobalPairQFinite_actual,
    ← monsterNortonShortQSource_actual]
  exact generatedAxisGlobalFifthRoot00FirstPair_QImage s i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
