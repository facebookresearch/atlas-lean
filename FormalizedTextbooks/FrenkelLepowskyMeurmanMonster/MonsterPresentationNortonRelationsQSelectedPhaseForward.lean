/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact selected central phases for the actual forward Norton Q evaluator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

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

/-- Packed genuine cocycle pairings of the actual forward coordinate-generator images. -/
def monsterNortonUQForwardPairMasks : Fin 24 → ℕ :=
  ![1024, 49152, 8430592, 8414208, 1360896, 2671616, 1164288, 2278400,
    377856, 705536, 3069, 1024, 1, 14, 1022, 1022,
    336, 672, 336, 672, 336, 672, 1024, 2060]

/-- The exact forward generator pairing is read from its certified row mask. -/
def monsterNortonUQForwardPairPhase (i j : Fin 24) : ZMod 2 :=
  if (monsterNortonUQForwardPairMasks i).testBit j.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Verify all 576 actual forward-generator pairings.
/-- These finite scalar values equal the actual cocycle pairings of all forward images. -/
theorem monsterNortonUQForwardPairPhase_actual (i j : Fin 24) :
    qBeta (toAdd (monsterNortonUQGeneratorImage i).base)
      (toAdd (monsterNortonUQGeneratorImage j).base) =
        monsterNortonUQForwardPairPhase i j := by
  revert i j
  decide +kernel

/-- The full actual forward evaluator central coefficient is its exact selected scalar phase. -/
theorem monsterNortonUQFastImage_selected_phase (q : Q) :
    toAdd (monsterNortonUQFastImage q).coeff =
      toAdd q.coeff + monsterNortonQSelectedPhase monsterNortonCoordinatePairPhase
        (toAdd q.base) (List.finRange 24) +
      monsterNortonQSelectedPhase monsterNortonUQForwardPairPhase
        (toAdd q.base) (List.finRange 24) := by
  have hc : ∀ i, toAdd (qCoordinateGenerator i).coeff = (0 : ZMod 2) := by
    intro i
    rfl
  have hi : ∀ i, toAdd (monsterNortonUQGeneratorImage i).coeff = (0 : ZMod 2) := by
    intro i
    fin_cases i <;> rfl
  rw [monsterNortonUQFastImage, monsterNortonCoordinateEvaluation_finite_phase,
    List.ofFn_eq_map, List.ofFn_eq_map,
    selected_actual _ _ hc monsterNortonCoordinatePairPhase_actual,
    selected_actual _ _ hi monsterNortonUQForwardPairPhase_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
