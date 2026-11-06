/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original pair and tensor reads of preferred basis ten's inverse packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortExtraTensorPairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete integer numerator of each actual transported pair-short entry. -/
def monsterNortonCodeTenInverseShortRead (p : Fin 2 × Fin 128) : ℤ :=
  (if p.1 = 0 then -1 else 1) *
    (monsterNortonUNumerator1 (monsterNortonCodeTenInversePairFirst p.2) 0 *
      monsterNortonUNumerator1 (monsterNortonCodeTenInversePairSecond p.2) 16 +
      monsterNortonUNumerator1 (monsterNortonCodeTenInversePairFirst p.2) 16 *
      monsterNortonUNumerator1 (monsterNortonCodeTenInversePairSecond p.2) 0)

set_option maxHeartbeats 16000000 in
-- All 256 pair rows are checked against the actual two physical U columns.
/-- The entire transported physical matrix gives every inverse candidate short coefficient. -/
theorem monsterNortonCodeTenInverseShortRead_coefficient (p : Fin 2 × Fin 128) :
    monsterNortonCodeTenInverseShortRead p =
      monsterNortonCodeTenInverseShortCoefficient p.1 p.2 := by
  revert p
  decide +kernel

/-- The complete numerator of both genuine odd source columns in an inverse tensor entry. -/
def monsterNortonCodeTenInverseTensorRead (p : Fin 4 × Fin 1) : ℤ :=
  let n := monsterNortonCodeTenInverseSpinLabel p.1
  let j := monsterNortonCodeTenInverseColumns p.2
  (-16 : ℤ) * (if n.val < 2048 then 1 else -1) *
    ((if j = 3 ∧ n.val % 2048 = 338 then
      if (golayEncodedMask 338).testBit j.val then -1 else 1 else 0) +
    (if j = 3 ∧ n.val % 2048 = 82 then
      if (golayEncodedMask 82).testBit j.val then -1 else 1 else 0))

/-- Both actual odd source columns give precisely the four proposed tensor coefficients. -/
theorem monsterNortonCodeTenInverseTensorRead_coefficient (p : Fin 4 × Fin 1) :
    monsterNortonCodeTenInverseTensorRead p = monsterNortonCodeTenInverseTensorCoefficient p := by
  revert p
  decide +kernel

private def VSourcePhase (q : Q) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd q.base) +
    qBeta (toAdd q.base) (toAdd y555NortonVQ.base)

private theorem source_phase (d : Fin 2048) :
    monsterNortonVShortPhase (Sum.inr (Sum.inr (d, 3))) =
      VSourcePhase (monsterNortonShortQSource (Sum.inr (Sum.inr (d, 3)))) := by
  unfold monsterNortonVShortPhase VSourcePhase
  rw [monsterNortonShortQSource_eq]

/-- The two source outputs retain their genuine negative Norton V phases. -/
theorem monsterNortonCodeTenInverseSourcePhases :
    qSign (monsterNortonVShortPhase (Sum.inr (Sum.inr (338, 3)))) = (-1 : ℝ) ∧
      qSign (monsterNortonVShortPhase (Sum.inr (Sum.inr (82, 3)))) = (-1 : ℝ) := by
  have h : VSourcePhase (monsterNortonShortQSource (Sum.inr (Sum.inr (338, 3)))) = 1 ∧
      VSourcePhase (monsterNortonShortQSource (Sum.inr (Sum.inr (82, 3)))) = 1 := by
    decide +kernel
  rw [source_phase, source_phase, h.1, h.2, qSign_one]
  exact ⟨rfl, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
