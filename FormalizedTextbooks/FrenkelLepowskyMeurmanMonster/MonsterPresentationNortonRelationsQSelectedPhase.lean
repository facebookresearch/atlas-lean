/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Scalar phase evaluation from the selected coordinate factors and their certified pairings. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQFinitePhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCacheInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The phase of coefficient-zero factors selected by an arbitrary binary vector. -/
def monsterNortonQSelectedPhase (p : Fin 24 → Fin 24 → ZMod 2)
    (v : Fin 24 → ZMod 2) : List (Fin 24) → ZMod 2
  | [] => 0
  | i :: l => monsterNortonQSelectedPhase p v l +
      if v i = 0 then 0 else (l.map (fun j => if v j = 0 then 0 else p i j)).sum

private theorem selected_actual (images : Fin 24 → Q)
    (p : Fin 24 → Fin 24 → ZMod 2)
    (hc : ∀ i, toAdd (images i).coeff = 0)
    (hp : ∀ i j, qBeta (toAdd (images i).base) (toAdd (images j).base) = p i j)
    (v : Fin 24 → ZMod 2) (l : List (Fin 24)) :
    monsterNortonQFinitePhase (l.map (fun i => if v i = 0 then 1 else images i)) =
      monsterNortonQSelectedPhase p v l := by
  have hb : toAdd (1 : Q).base = 0 := rfl
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : v i = 0
    · simp [monsterNortonQFinitePhase, monsterNortonQSelectedPhase, hi,
        qBeta_zero_left, ih, Function.comp_def]
    · simp only [List.map_cons, monsterNortonQFinitePhase, hi, ite_false, hc,
        zero_add, ih, monsterNortonQSelectedPhase]
      congr 1
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro j _
      by_cases hj : v j = 0
      · simp only [hj, ite_true, Function.comp_apply, hb, qBeta_zero_right]
      · simp only [hj, ite_false, Function.comp_apply, hp]

/-- Binary row masks of the genuine inverse-image pairings for the coordinate generators. -/
def monsterNortonUQInversePairMasks : Fin 24 → ℕ :=
  ![1048576, 327680, 720896, 917504, 311296, 811008, 114688, 237568,
    1048576, 11534336, 0, 1048576, 1, 162, 116, 216,
    214, 172, 122, 172, 4196865, 0, 9438208, 4196864]

/-- Exact pairings of the original positive coordinate lifts. -/
def monsterNortonCoordinatePairPhase (i j : Fin 24) : ZMod 2 :=
  if i.val < 12 ∧ j.val = i.val + 12 then 1 else 0

/-- Exact scalar pairings of the actual signed inverse Norton generator images. -/
def monsterNortonUQInversePairPhase (i j : Fin 24) : ZMod 2 :=
  if (monsterNortonUQInversePairMasks i).testBit j.val then 1 else 0

set_option maxHeartbeats 16000000 in
-- Verify every one of the 576 actual original-generator pairings.
/-- The original coordinate-pair phase table is the genuine cocycle pairing. -/
theorem monsterNortonCoordinatePairPhase_actual (i j : Fin 24) :
    qBeta (toAdd (qCoordinateGenerator i).base) (toAdd (qCoordinateGenerator j).base) =
      monsterNortonCoordinatePairPhase i j := by
  revert i j
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Verify all 576 inverse-generator pairings through their actual full coordinate images.
/-- The inverse pairing table is exactly the actual cocycle pairing of the generator images. -/
theorem monsterNortonUQInversePairPhase_actual (i j : Fin 24) :
    qBeta (toAdd (monsterNortonUQInverseGeneratorImage i).base)
      (toAdd (monsterNortonUQInverseGeneratorImage j).base) =
        monsterNortonUQInversePairPhase i j := by
  revert i j
  decide +kernel

/-- The selected scalar tables give the full actual inverse evaluator coefficient. -/
theorem monsterNortonUQInverseFastImage_selected_phase (q : Q) :
    toAdd (monsterNortonUQInverseFastImage q).coeff =
      toAdd q.coeff + monsterNortonQSelectedPhase monsterNortonCoordinatePairPhase
        (toAdd q.base) (List.finRange 24) +
      monsterNortonQSelectedPhase monsterNortonUQInversePairPhase
        (toAdd q.base) (List.finRange 24) := by
  have hc : ∀ i, toAdd (qCoordinateGenerator i).coeff = (0 : ZMod 2) := by
    intro i
    rfl
  have hi : ∀ i, toAdd (monsterNortonUQInverseGeneratorImage i).coeff = (0 : ZMod 2) := by
    intro i
    fin_cases i <;> rfl
  rw [monsterNortonUQInverseFastImage, monsterNortonCoordinateEvaluation_finite_phase,
    List.ofFn_eq_map, List.ofFn_eq_map,
    selected_actual _ _ hc monsterNortonCoordinatePairPhase_actual,
    selected_actual _ _ hi monsterNortonUQInversePairPhase_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
