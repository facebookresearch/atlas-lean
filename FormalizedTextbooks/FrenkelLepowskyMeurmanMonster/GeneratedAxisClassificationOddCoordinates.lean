/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairTensor

/-! Physical matrix and tensor coordinates of the actual odd-family triality image.
The spatial line and the two-point Hadamard spin state are derived from the
original Conway dictionary, without assigning a conjugacy-class name. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original odd short vector has diagonal square 9/4 at its distinguished
coordinate and 1/4 at every other coordinate. -/
theorem generatedAxis_odd_axial_diagonal (d : Fin 2048) (i j : Fin 24) :
    2 * griessShortVector (Sum.inr (Sum.inr (d, i))) j *
      griessShortVector (Sum.inr (Sum.inr (d, i))) j =
        1 / 4 + if j = i then 2 else 0 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  simp only [griessShortVector, mul_assoc, div_mul_div_comm, hs, griessShortIntegral]
  split_ifs <;> norm_num

/-- The actual odd transition matrix is a scalar matrix plus twice a coordinate-line projector. -/
theorem generatedAxis_triality_odd_matrix (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))).1 =
      Matrix.diagonal (fun j : Fin 24 => 1 / 4 + if j = i then (2 : ℝ) else 0) := by
  have hcycle : trialityCycle.symm 0 = 2 := by decide
  funext j k
  by_cases hjk : j = k
  · subst k
    simpa [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, Matrix.diagonal, Matrix.vecMulVec_apply,
      mul_assoc] using generatedAxis_odd_axial_diagonal d i j
  · simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, hcycle, Matrix.diagonal, hjk]

/-- The actual odd transition tensor is its original Y Hadamard basis state,
scaled by the signed axis coefficient. -/
theorem generatedAxis_triality_odd_tensor (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))).2.2 =
      (-8 * qSign c : ℝ) • trialityYTensor d i := by
  have h1 : trialityCycle.symm 1 = 0 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  funext t j
  by_cases hd : spinDictionaryCode t = d <;> by_cases hj : j = i
  all_goals
    simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h1, h2, hd, hj,
      trialityYTensor, Pi.single_apply]
  split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
