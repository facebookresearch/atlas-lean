/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-generator dictionary actions needed for triality-word comparison. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Square

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An encoded physical coordinate is exactly its actual binary singleton character. -/
theorem monsterCode_coordinate_character (a : SpinIndex) (i : Fin 24) :
    spinDot a (fun k => (golayGeneratorBit k i : ZMod 2)) = golayEncoder a i := rfl

/-- The actual Q code action on an odd short lift has the exact source commutator character. -/
theorem monsterSourceCode_odd_phase (d : Fin 4096) (ε : ZMod 2)
    (e : Fin 2048) (i : Fin 24) :
    localShortPhase (localFiberIncl (sourceQCode d ε)) (Sum.inr (Sum.inr (e,i))) =
      spinDot (golayLabelCoefficients d) (sourceWordTheta ⟨e.val, by omega⟩) +
        spinDot (golayLabelCoefficients ⟨e.val, by omega⟩)
          (sourceCodeThetaPolynomial (golayLabelCoefficients d)) +
        golayEncoder (golayLabelCoefficients d) i := by
  change toAdd (spinConjugation (spinHolomorphIncl (sourceQCode d ε))
    (griessShortQ (Sum.inr (Sum.inr (e,i))))).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero, qBeta_spin_coordinates, qBeta_spin_coordinates,
    sourceQCode_translation, sourceQCode_modulation, griessOdd_translation,
    griessOdd_modulation, spinDot_add_right, spinDot_add_left, xiSpinDot_smul_left,
    monsterCode_coordinate_character]
  have hθ : spinDot (Pi.single 11 1)
      (sourceCodeThetaPolynomial (golayLabelCoefficients d)) = 0 := by
    rw [spinDot_comm, ← sourceWordTheta_eq_polynomial, sourceWordTheta_dot_omega]
  rw [hθ, mul_zero, add_zero]
  abel

/-- The source code therefore acts on every actual odd short coordinate by this exact sign. -/
theorem monsterSourceCode_short_odd (d : Fin 4096) (ε : ZMod 2)
    (x : GriessShortIndex → ℝ) (e : Fin 2048) (i : Fin 24) :
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) x
      (Sum.inr (Sum.inr (e,i))) =
      qSign (spinDot (golayLabelCoefficients d) (sourceWordTheta ⟨e.val, by omega⟩) +
        spinDot (golayLabelCoefficients ⟨e.val, by omega⟩)
          (sourceCodeThetaPolynomial (golayLabelCoefficients d)) +
        golayEncoder (golayLabelCoefficients d) i) * x (Sum.inr (Sum.inr (e,i))) := by
  have hp : griessShortPermutation (localFiberIncl (sourceQCode d ε)).val.2
      (Sum.inr (Sum.inr (e,i))) = Sum.inr (Sum.inr (e,i)) := by
    change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  have he := localShortOperator_image (localFiberIncl (sourceQCode d ε)) x
    (Sum.inr (Sum.inr (e,i)))
  rw [hp, monsterSourceCode_odd_phase] at he
  exact he

/-- The full actual code action on the X dictionary row is the source sign character. -/
theorem monsterSourceCode_blocks_X (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) (e : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode d ε)) x)).2.2.2 0
      (finProdFinEquiv (e,i)) =
      qSign (spinDot (golayLabelCoefficients d) (sourceWordTheta ⟨e.val, by omega⟩) +
        spinDot (golayLabelCoefficients ⟨e.val, by omega⟩)
          (sourceCodeThetaPolynomial (golayLabelCoefficients d)) +
        golayEncoder (golayLabelCoefficients d) i) *
          (trialityBlocksEquiv x).2.2.2 0 (finProdFinEquiv (e,i)) := by
  have he := localGriessRepresentation_encode (localFiberIncl (sourceQCode d ε)) x
  have hs := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inr (Sum.inr (e,i)))) he
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1
      (Sum.inr (Sum.inr (e,i))) =
    localShortRepresentation (localFiberIncl (sourceQCode d ε))
      (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (e,i))) at hs
  rw [monsterSourceCode_short_odd] at hs
  exact hs

/-- Actual dictionary triality moves all three XYZ coordinate rows by the source cycle. -/
theorem monsterTriality_XYZ_blocks (x : GriessSpace) (a : Fin 3) (k : Fin 49152) :
    (trialityBlocksEquiv (sExtra x)).2.2.2 a k =
      (trialityBlocksEquiv x).2.2.2 (trialityCycle.symm a) k := by
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply]
  rfl

/-- The inverse dictionary triality has the exact reverse coordinate cycle. -/
theorem monsterTriality_inverse_XYZ_blocks (x : GriessSpace) (a : Fin 3) (k : Fin 49152) :
    (trialityBlocksEquiv (sExtra⁻¹ x)).2.2.2 a k =
      (trialityBlocksEquiv x).2.2.2 (trialityCycle a) k := by
  have h := monsterTriality_XYZ_blocks (sExtra.symm x) (trialityCycle a) k
  rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The actual literal inverse-transpose y word has the primary diagonal Y-row action. -/
theorem monsterSourceYWord_blocks_Y (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) (e : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode d ε)) * sExtra⁻¹) x)).2.2.2 1
        (finProdFinEquiv (e,i)) =
      qSign (spinDot (golayLabelCoefficients d) (sourceWordTheta ⟨e.val, by omega⟩) +
        spinDot (golayLabelCoefficients ⟨e.val, by omega⟩)
          (sourceCodeThetaPolynomial (golayLabelCoefficients d)) +
        golayEncoder (golayLabelCoefficients d) i) *
          (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (e,i)) := by
  have h0 : trialityCycle.symm 1 = 0 := by decide +kernel
  have h1 : trialityCycle 0 = 1 := by decide +kernel
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, monsterTriality_XYZ_blocks, h0,
    monsterSourceCode_blocks_X, monsterTriality_inverse_XYZ_blocks, h1]

/-- The code action fixes the actual A matrix row. -/
theorem monsterSourceCode_blocks_A (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 0 p =
      (trialityBlocksEquiv x).2.1 0 p := by
  have he := localGriessRepresentation_encode (localFiberIncl (sourceQCode d ε)) x
  have hm := congrArg (fun b : ConwayRawSpace => b.1) he
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).1 =
    conwayMatrixAction 1 (griessConwayEncode x).1 at hm
  rw [map_one] at hm
  have hp := congrFun (congrFun hm (griessCoordinatePair p).1) (griessCoordinatePair p).2
  simpa only [griessConwayEncode, dite_false, griessCoordinatePair_ne,
    griessPairIndex_pair, LinearEquiv.coe_one, id_eq] using hp

/-- The C row has the same verified character as the source B row. -/
theorem monsterSourceCode_blocks_C (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 2 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 2 p := by
  have he := localGriessRepresentation_encode (localFiberIncl (sourceQCode d ε)) x
  have h0 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (0,p))) he
  have h1 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (1,p))) he
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 (Sum.inl (0,p)) =
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) (griessConwayEncode x).2.1
      (Sum.inl (0,p)) at h0
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 (Sum.inl (1,p)) =
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) (griessConwayEncode x).2.1
      (Sum.inl (1,p)) at h1
  rw [sourceQCode_short_pair] at h0 h1
  simp only [griessConwayEncode, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h0 h1
  linarith

/-- Actual triality cycles every A,B,C dictionary coordinate. -/
theorem monsterTriality_ABC_blocks (x : GriessSpace) (a : Fin 3) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra x)).2.1 a p =
      (trialityBlocksEquiv x).2.1 (trialityCycle.symm a) p := by
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply]
  rfl

/-- Inverse triality reverses the same A,B,C coordinate cycle. -/
theorem monsterTriality_inverse_ABC_blocks (x : GriessSpace) (a : Fin 3) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra⁻¹ x)).2.1 a p =
      (trialityBlocksEquiv x).2.1 (trialityCycle a) p := by
  have h := monsterTriality_ABC_blocks (sExtra.symm x) (trialityCycle a) p
  rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The literal source y word fixes B and scales A,C by its genuine physical code sign. -/
theorem monsterSourceYWord_blocks_ABC (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) (a : Fin 3) (p : Fin 276) :
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode d ε)) * sExtra⁻¹) x)).2.1 a p =
      (if a = 1 then 1 else
        qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
          golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2)) *
            (trialityBlocksEquiv x).2.1 a p := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, monsterTriality_ABC_blocks]
  have hc : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide +kernel
  rcases hc a with rfl | rfl | rfl
  · have hs : trialityCycle.symm 0 = 2 := by decide +kernel
    have hf : trialityCycle 2 = 0 := by decide +kernel
    rw [hs, monsterSourceCode_blocks_C, monsterTriality_inverse_ABC_blocks, hf]
    simp
  · have hs : trialityCycle.symm 1 = 0 := by decide +kernel
    have hf : trialityCycle 0 = 1 := by decide +kernel
    rw [hs, monsterSourceCode_blocks_A, monsterTriality_inverse_ABC_blocks, hf]
    simp
  · have hs : trialityCycle.symm 2 = 1 := by decide +kernel
    have hf : trialityCycle 1 = 2 := by decide +kernel
    rw [hs, sourceQCode_blocks_B, monsterTriality_inverse_ABC_blocks, hf]
    simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
