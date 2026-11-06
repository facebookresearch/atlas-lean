/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates

/-! The actual odd-family triality image has short support in the pair family. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original odd outer square gives the pair-short coordinates of its triality image. -/
theorem generatedAxis_triality_odd_pair_coordinate
    (d : Fin 2048) (i : Fin 24) (c : ZMod 2) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))).2.1
      (Sum.inl (s, p)) =
        (if s = 0 then 1 else -1) *
          (2 * griessShortVector (Sum.inr (Sum.inr (d, i))) (griessCoordinatePair p).1 *
            griessShortVector (Sum.inr (Sum.inr (d, i))) (griessCoordinatePair p).2) := by
  have h1 : trialityCycle.symm 1 = 0 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  fin_cases s <;>
    simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h1, h2,
      Matrix.vecMulVec_apply, mul_assoc]

/-- No octad-short coordinate survives the actual odd-family transition. -/
theorem generatedAxis_triality_odd_octad_coordinate
    (d : Fin 2048) (i : Fin 24) (c : ZMod 2) (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))).2.1
      (Sum.inr (Sum.inl (o, e))) = 0 := by
  suffices h : trialityOctadAction (fun _ : Fin 64 => (0 : ℝ)) e = 0 by
    simpa [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction] using h
  exact congrFun (map_zero trialityOctadAction) e

/-- No odd-short coordinate survives the actual odd-family transition. -/
theorem generatedAxis_triality_odd_odd_coordinate
    (d f : Fin 2048) (i j : Fin 24) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))).2.1
      (Sum.inr (Sum.inr (f, j))) = 0 := by
  have h0 : trialityCycle.symm 0 = 2 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
    conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h0]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
