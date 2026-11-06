/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact denominator-sixteen coordinates at the first pair-short seventh state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairOctadV
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Integer realization of an actual central Q phase. -/
def monsterNortonLine01PairPhaseSign (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

/-- Its cast is precisely the actual real sign, for every phase. -/
theorem monsterNortonLine01PairPhaseSign_cast (c : ZMod 2) :
    (monsterNortonLine01PairPhaseSign c : ℝ) = qSign c := by
  simp only [monsterNortonLine01PairPhaseSign, qSign, Int.cast_ite, Int.cast_one,
    Int.cast_neg]

/-- The full integer numerator of each true sixth-state source summand. -/
def monsterNortonLine01PairSixthNumerator (e : Fin 64) : ℤ :=
  monsterNortonLine01PairOctadInverseNumerator e *
    monsterNortonLine01PairPhaseSign (monsterNortonLine01PairOctadVPhase e) *
      monsterNortonLine01PairPhaseSign (monsterNortonLine01PairInverseVPhase e)

/-- The eight symmetric off-diagonal matrix numerators in the physical seventh state. -/
def monsterNortonLine01PairSeventhMatrixNumerator : Fin 8 → ℤ :=
  ![-1, 1, -1, 1, -1, 1, -1, 1]

/-- Both physical pair-family numerators for each adjacent coordinate pair. -/
def monsterNortonLine01PairSeventhPairNumerator : Fin 2 → Fin 8 → ℤ :=
  ![![-1, -1, -1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, -1, -1, -1]]

/-- All original octad numerators, including every zero, in the fourteen reached blocks. -/
def monsterNortonLine01PairSeventhOctadNumerator : Fin 14 → Fin 64 → ℤ :=
  ![![
      0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0],
    ![
      0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0],
    ![
      0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0],
    ![
      -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1,
      0, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0,
      1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1],
    ![
      0, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1,
      1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0],
    ![
      0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0,
      0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0,
      0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0],
    ![
      0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0,
      0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0],
    ![
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0],
    ![
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0],
    ![
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0],
    ![
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0,
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0],
    ![
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
    ![
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
      0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![
      0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, 0, 0, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
      0, 0, 0, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0, 0, 0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Verify all 896 scalar Fourier outputs from the exact integer input and V phases.
/-- Every nonzero and zero octad numerator agrees with the actual sixty-four-term transform. -/
theorem monsterNortonLine01PairSeventhOctadNumerator_certificate (a : Fin 14) (r : Fin 64) :
    (∑ e : Fin 64,
      if monsterNortonLine01PairInverseIsPair e then 0
      else if monsterNortonLine01PairInverseOctadSlot e = a then
        monsterNortonLine01PairSixthNumerator e *
          (if trialityBitWeight8 (trialityEvenMask r) / 2 % 2 = 0 then (1 : ℤ) else -1) *
            trialityHadamard r (monsterNortonLine01PairInverseOctadSign e)
      else 0) = 4 * monsterNortonLine01PairSeventhOctadNumerator a r := by
  revert a r
  decide +kernel

set_option maxRecDepth 10000 in
/-- All eight matrix numerators agree with the actual reached pair-summand coefficients. -/
theorem monsterNortonLine01PairSeventhMatrixNumerator_certificate (k : Fin 8) :
    (∑ e : Fin 64,
      if monsterNortonLine01PairInverseIsPair e &&
          (monsterNortonLine01PairInversePairFirst e).val == 2 * k.val then
        monsterNortonLine01PairSixthNumerator e else 0) =
      monsterNortonLine01PairSeventhMatrixNumerator k := by
  revert k
  decide +kernel

set_option maxRecDepth 10000 in
/-- The two actual pair-family output coefficients have exactly these integer numerators. -/
theorem monsterNortonLine01PairSeventhPairNumerator_certificate (s : Fin 2) (k : Fin 8) :
    (∑ e : Fin 64,
      if monsterNortonLine01PairInverseIsPair e &&
          (monsterNortonLine01PairInversePairFirst e).val == 2 * k.val then
        monsterNortonLine01PairSixthNumerator e *
          (if monsterNortonLine01PairInversePairSign e = 0 then (1 : ℤ) else -1)
      else 0) = monsterNortonLine01PairSeventhPairNumerator s k := by
  revert s k
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
