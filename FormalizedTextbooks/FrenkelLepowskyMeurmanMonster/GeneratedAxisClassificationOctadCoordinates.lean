/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits

/-! The actual octad transition's eight-dimensional matrix projection. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual octad coordinates have axial diagonal one on their support. -/
theorem generatedAxis_octad_axial_diagonal (o : Fin 759) (e : Fin 64) (i : Fin 24) :
    2 * griessShortVector (Sum.inr (Sum.inl (o, e))) i *
      griessShortVector (Sum.inr (Sum.inl (o, e))) i =
        if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 1 else 0 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  simp only [griessShortVector, mul_assoc, div_mul_div_comm, hs, griessShortIntegral]
  split_ifs <;> norm_num

/-- Triality sends the actual octad-axis matrix to its eight-coordinate
orthogonal projection; the original signs disappear from this matrix block. -/
theorem generatedAxis_triality_octad_matrix (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 =
      Matrix.diagonal (fun i : Fin 24 =>
        if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 1 else 0) := by
  have hcycle : trialityCycle.symm 0 = 2 := by decide
  funext i j
  by_cases hij : i = j
  · subst j
    simpa [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, Matrix.diagonal, Matrix.vecMulVec_apply,
      mul_assoc] using generatedAxis_octad_axial_diagonal o e i
  · simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, hcycle, Matrix.diagonal, hij]

/-- Actual pair-short coordinates in an octad transition come from the
original octad outer square, with opposite signs on the two pair labels. -/
theorem generatedAxis_triality_octad_pair_coordinate
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1
      (Sum.inl (s, p)) =
        (if s = 0 then 1 else -1) *
          (2 * griessShortVector (Sum.inr (Sum.inl (o, e))) (griessCoordinatePair p).1 *
            griessShortVector (Sum.inr (Sum.inl (o, e))) (griessCoordinatePair p).2) := by
  have h1 : trialityCycle.symm 1 = 0 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  fin_cases s <;>
    simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h1, h2,
      Matrix.vecMulVec_apply, mul_assoc]

/-- The actual octad transition has no odd-family short coordinates. -/
theorem generatedAxis_triality_octad_odd_coordinate
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1
      (Sum.inr (Sum.inr (d, i))) = 0 := by
  have h0 : trialityCycle.symm 0 = 2 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
    conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h0]

/-- The projection matrix has trace eight, checked on the actual octad support. -/
theorem generatedAxis_triality_octad_matrix_trace (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    Matrix.trace (griessConwayEncode
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 = 8 := by
  rw [generatedAxis_triality_octad_matrix, Matrix.trace_diagonal]
  have hw := golayOctad_support_card o
  rw [golayMaskSupport_card] at hw
  exact_mod_cast hw

/-- Every Fourier coordinate on the same octad has squared value one. -/
theorem generatedAxis_triality_octad_same_coordinate_square
    (o : Fin 759) (e f : Fin 64) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1
      (Sum.inr (Sum.inl (o, f))) ^ 2 = 1 := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change (trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 o) f) ^ 2 = _
  have hrow : (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 o =
      (-8 * qSign c : ℝ) • Pi.single e 1 := by
    funext t
    by_cases ht : t = e <;> simp [conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, Pi.single_apply, ht]
  rw [hrow, map_smul]
  simp only [trialityOctadAction, LinearEquiv.trans_apply, trialityHadamardEquiv,
    trialitySignEquiv, trialityNormalizedHadamard]
  fin_cases c
  all_goals
    simp [qSign, trialityHadamard, trialityEvenMask, trialityBitWeight8]

/-- Triality does not introduce coordinates on a different octad. -/
theorem generatedAxis_triality_octad_other_coordinate
    (o p : Fin 759) (e f : Fin 64) (c : ZMod 2) (hp : p ≠ o) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1
      (Sum.inr (Sum.inl (p, f))) = 0 := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 p) f = _
  have hrow : (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 p = 0 := by
    funext t
    simp [conwayShortAxis, griessConwayDecode, conwayShortAxisRaw, Pi.single_apply, hp]
  rw [hrow, map_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
