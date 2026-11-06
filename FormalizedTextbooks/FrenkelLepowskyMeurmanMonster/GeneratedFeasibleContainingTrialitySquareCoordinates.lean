/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingRootedSectionPhaseFibers

/-! Actual coordinates of the second triality image of an original signed octad axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual second triality image of the original containing octad prototype. -/
def generatedFeasibleContainingTrialitySquare : GriessSpace :=
  sExtra generatedFeasibleContainingOctadDestination

/-- The corresponding original old-octad second triality image. -/
def generatedFeasibleContainingOldTrialitySquare : GriessSpace :=
  sExtra (generatedOctadLocalAxis 0 0)

/-- Two original triality operations are exactly the inverse original operation. -/
theorem generatedFeasibleContaining_triality_square_inverse (x : GriessSpace) :
    sExtra (sExtra x) = sExtra.symm x := by
  apply sExtra.injective
  have h := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace => e x) sExtra_pow_three
  change sExtra (sExtra (sExtra x)) = x at h
  rw [h, LinearEquiv.apply_symm_apply]

/-- The genuine second octad triality image has the same actual eight-coordinate projector. -/
theorem generatedFeasibleContaining_triality_square_matrix
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    (griessConwayEncode
      (sExtra (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).1 =
      Matrix.diagonal (fun i : Fin 24 =>
        if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 1 else 0) := by
  have h0 : trialityCycle.symm 0 = 2 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  funext i j
  by_cases hij : i = j
  · subst j
    simpa [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, Matrix.diagonal, Matrix.vecMulVec_apply,
      mul_assoc] using generatedAxis_octad_axial_diagonal o e i
  · simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h0, h2,
      Matrix.diagonal, hij]

/-- Both preferred pair signs in the second image have the same original outer-square sign. -/
theorem generatedFeasibleContaining_triality_square_pair_coordinate
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode
      (sExtra (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.1
      (Sum.inl (s, p)) =
        2 * griessShortVector (Sum.inr (Sum.inl (o, e))) (griessCoordinatePair p).1 *
          griessShortVector (Sum.inr (Sum.inl (o, e))) (griessCoordinatePair p).2 := by
  have h0 : trialityCycle.symm 0 = 2 := by decide
  have h1 : trialityCycle.symm 1 = 0 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  fin_cases s <;>
    simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h0, h1, h2,
      Matrix.vecMulVec_apply, mul_assoc]

/-- No odd-family short coordinates occur in the genuine second octad image. -/
theorem generatedFeasibleContaining_triality_square_odd_coordinate
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode
      (sExtra (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.1
      (Sum.inr (Sum.inr (d, i))) = 0 := by
  have h0 : trialityCycle.symm 0 = 2 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
    conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, h0, h2]

/-- The second octad image still has its entire actual tensor coordinate zero. -/
theorem generatedFeasibleContaining_triality_square_tensor_zero
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    (griessConwayEncode
      (sExtra (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.2 = 0 := by
  funext t i
  simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
    conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, trialityCycle]

/-- The actual twice-applied octad block operation equals its certified inverse. -/
theorem generatedFeasibleContaining_octad_square_inverse (x : Fin 64 → ℝ) :
    trialityOctadAction (trialityOctadAction x) = trialityOctadAction.symm x := by
  apply trialityOctadAction.injective
  rw [trialityOctadAction_triple, LinearEquiv.apply_symm_apply]

/-- The original diagonal octad signs are their own actual inverse. -/
theorem generatedFeasibleContaining_octad_sign_inverse (x : Fin 64 → ℝ) :
    trialitySignEquiv.symm x = trialitySignEquiv x := by
  apply trialitySignEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  change x i = (if trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0 then (1 : ℝ) else -1) *
    ((if trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0 then (1 : ℝ) else -1) * x i)
  split_ifs <;> ring

/-- The inverse original octad action is diagonal signs followed by its actual Fourier map. -/
theorem generatedFeasibleContaining_octad_inverse_formula (x : Fin 64 → ℝ) :
    trialityOctadAction.symm x = trialityHadamardEquiv (trialitySignEquiv x) := by
  change trialityHadamardEquiv.symm (trialitySignEquiv.symm x) = _
  rw [generatedFeasibleContaining_octad_sign_inverse]
  rfl

/-- Original signed-octad coordinates in the second image all have square one. -/
theorem generatedFeasibleContaining_triality_square_octad_square
    (o : Fin 759) (e f : Fin 64) (c : ZMod 2) :
    (griessConwayEncode
      (sExtra (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.1
      (Sum.inr (Sum.inl (o, f))) ^ 2 = 1 := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change (trialityOctadAction (trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 o)) f) ^ 2 = _
  have hrow : (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 o =
      (-8 * qSign c : ℝ) • Pi.single e 1 := by
    funext t
    by_cases ht : t = e <;> simp [conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, Pi.single_apply, ht]
  rw [hrow, generatedFeasibleContaining_octad_square_inverse, map_smul,
    generatedFeasibleContaining_octad_inverse_formula]
  have hsign : trialitySignEquiv (Pi.single e 1) =
      (if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then (1 : ℝ) else -1) •
        Pi.single e 1 := by
    funext i
    by_cases hi : i = e <;> simp [trialitySignEquiv, hi]
  rw [hsign, map_smul]
  change ((-8 * qSign c) *
    ((if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then (1 : ℝ) else -1) *
      (trialityNormalizedHadamard *ᵥ Pi.single e 1) f)) ^ 2 = 1
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, trialityNormalizedHadamard]
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  unfold trialityHadamard
  split_ifs <;> fin_cases c <;> norm_num [qSign]

/-- A genuine second octad image has zero coordinates on every other octad block. -/
theorem generatedFeasibleContaining_triality_square_other_octad_coordinate
    (o p : Fin 759) (e f : Fin 64) (c : ZMod 2) (hp : p ≠ o) :
    (griessConwayEncode
      (sExtra (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.1
      (Sum.inr (Sum.inl (p, f))) = 0 := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change trialityOctadAction (trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 p)) f = _
  have hrow : (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 p = 0 := by
    funext t
    simp [conwayShortAxis, griessConwayDecode, conwayShortAxisRaw, Pi.single_apply, hp]
  rw [hrow, map_zero, map_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
