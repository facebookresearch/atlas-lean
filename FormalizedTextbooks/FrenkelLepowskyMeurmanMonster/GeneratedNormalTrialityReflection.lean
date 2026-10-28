/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Odd cocode reflection of the actual dictionary triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Reflection of the Y/Z rows with the X row fixed. -/
def trialityRowReflection : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Source coordinate signs of an odd cocode element on X,Y,Z. -/
noncomputable def cocodeXYZScalar (h : SpinIndex) (d : Fin 2048) (i : Fin 24) : ℝ :=
  qSign (spinDot h (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1)

/-- The full source dictionary reflection, before proving its equality with the local action. -/
noncomputable def cocodeDictionaryAction (h : SpinIndex) (b : TrialityBlocks) : TrialityBlocks :=
  (b.1, ((fun s p => b.2.1 (trialityRowReflection s) p),
    ((fun o e => qSign (spinDot h (golayLabelCoefficients (golayOctadLabel o))) *
      (trialityIntegerDiagonal e : ℝ) * b.2.2.1 o e),
    fun s k => let di : Fin 2048 × Fin 24 := finProdFinEquiv.symm k
      cocodeXYZScalar h di.1 di.2 * b.2.2.2 (trialityRowReflection s) k)))

lemma spinDot_single_last (h : SpinIndex) : spinDot h (Pi.single 11 1) = h 11 := by
  simp [spinDot, Pi.single_apply]

private lemma cocodeQ_odd_phase_of_index (h : SpinIndex) (hh : h 11 = 1)
    (d : Fin 2048) (t : SpinIndex)
    (hi : t = golayLabelCoefficients ⟨d.val, by omega⟩ ∨
      t = golayLabelCoefficients ⟨d.val + 2048, by omega⟩) :
    qSign (spinDot h t) =
      qSign (spinDot h (golayLabelCoefficients ⟨d.val, by omega⟩)) * qSign (t 11) := by
  rcases hi with ht | ht
  · simp only [ht, golayLabel_low_last, qSign_zero, mul_one]
  · conv_lhs => rw [ht, ← golayLabel_low_add_omega]
    rw [spinDot_add_right, qSign_add, spinDot_single_last, hh]
    simp only [ht, golayLabel_high_last]

lemma cocodeQ_odd_phase (h : SpinIndex) (hh : h 11 = 1) (t : SpinIndex) :
    qSign (spinDot h t) =
      qSign (spinDot h (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩)) *
        qSign (t 11) :=
  cocodeQ_odd_phase_of_index h hh (spinDictionaryCode t) t (spinDictionaryIndex_cases t)

lemma cocodeQ_odd_short_phase (h : SpinIndex) (hh : h 11 = 1)
    (d : Fin 2048) (i : Fin 24) :
    qSign (spinDot h (spinTranslation (griessShortQ (Sum.inr (Sum.inr (d,i)))))) =
      cocodeXYZScalar h d i := by
  rw [griessOdd_translation, spinDot_add_right, spinDot_smul_right,
    spinDot_single_last, hh, mul_one, qSign_add,
    griessOddOmegaCoefficient_quarter, qSign_add, golayEncoder_low_qSign]
  unfold cocodeXYZScalar
  ring

lemma cocodeQ_octad_short_phase (h : SpinIndex) (hh : h 11 = 1)
    (o : Fin 759) (e : Fin 64) :
    qSign (spinDot h (spinTranslation (griessShortQ (Sum.inr (Sum.inl (o,e)))))) =
      qSign (spinDot h (golayLabelCoefficients (golayOctadLabel o))) *
        (trialityIntegerDiagonal e : ℝ) := by
  rw [griessOctad_translation, spinDot_add_right, spinDot_smul_right,
    spinDot_single_last, hh, mul_one, qSign_add]
  congr 1
  rw [griessOctadOmegaCoefficient_sign]

lemma cocodeXYZScalar_square (h : SpinIndex) (d : Fin 2048) (i : Fin 24) :
    cocodeXYZScalar h d i ^ 2 = 1 := by
  unfold cocodeXYZScalar
  rw [mul_pow, mul_pow]
  simp only [pow_two, qSign_sq, one_mul]
  split_ifs <;> norm_num

/-- The actual local odd cocode action agrees with every row of the source dictionary. -/
theorem cocodeQ_blocks (h : SpinIndex) (hh : h 11 = 1) (x : GriessSpace) :
    trialityBlocksEquiv (rhoLocal (inclQ (cocodeQ h)) x) =
      cocodeDictionaryAction h (trialityBlocksEquiv x) := by
  apply trialityBlocksEquiv.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (rhoLocal (inclQ (cocodeQ h)) x) =
    griessConwayEncode (trialityBlocksEquiv.symm (cocodeDictionaryAction h (trialityBlocksEquiv x)))
  rw [show rhoLocal (inclQ (cocodeQ h)) = localGriessRepresentation
      (localFiberIncl (cocodeQ h)) from rfl, localGriessRepresentation_encode,
    localConwayRawRepresentation_apply]
  change (conwayMatrixAction 1 (griessConwayEncode x).1, _) = _
  rw [map_one]
  apply Prod.ext
  · simp only [griessConwayEncode, LinearEquiv.apply_symm_apply, cocodeDictionaryAction]
    rfl
  · apply Prod.ext
    · funext r
      change localShortRepresentation (localFiberIncl (cocodeQ h))
        (griessConwayEncode x).2.1 r = _
      rw [cocodeQ_short]
      rcases r with ⟨s,p⟩ | (⟨o,e⟩ | ⟨d,i⟩)
      · rw [griessPairQ_translation]
        fin_cases s
        · simp [griessConwayEncode, cocodeDictionaryAction, trialityRowReflection,
            spinDot, LinearEquiv.apply_symm_apply]
          ring
        · simp [griessConwayEncode, cocodeDictionaryAction, trialityRowReflection,
            spinDot_single_last, hh, LinearEquiv.apply_symm_apply, qSign_one]
      · rw [cocodeQ_octad_short_phase h hh]
        simp only [griessConwayEncode, cocodeDictionaryAction, LinearEquiv.apply_symm_apply]
      · rw [cocodeQ_odd_short_phase h hh]
        have h0 : trialityRowReflection 0 = 0 := by decide
        simp only [griessConwayEncode, cocodeDictionaryAction, h0,
          LinearEquiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
    · funext t i
      change localTensorRepresentation (localFiberIncl (cocodeQ h))
        (griessConwayEncode x).2.2 t i = _
      rw [cocodeQ_tensor, cocodeQ_odd_phase h hh]
      simp only [griessConwayEncode, cocodeDictionaryAction, LinearEquiv.apply_symm_apply,
        finProdFinEquiv.symm_apply_apply, cocodeXYZScalar]
      simp only [trialityRowReflection, Equiv.swap_apply_right, Equiv.swap_apply_left]
      have hc := qSign_sq (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ)
      have ht := qSign_sq (t 11)
      have hm : (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then
          (-1 : ℝ) else 1) ^ 2 = 1 := by split_ifs <;> norm_num
      have hc2 := (show qSign (golayMaskWeight
        (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) ^ 2 = 1 by
          simpa only [pow_two] using hc)
      have ht2 := (show qSign (t 11) ^ 2 = 1 by simpa only [pow_two] using ht)
      ring_nf
      simp only [hc2, ht2, hm, mul_one]

lemma trialitySignEquiv_double (x : Fin 64 → ℝ) :
    trialitySignEquiv (trialitySignEquiv x) = x := by
  funext i
  change (if trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0 then (1 : ℝ) else -1) *
    ((if trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0 then (1 : ℝ) else -1) * x i) = x i
  split_ifs <;> ring

lemma trialityHadamardEquiv_double (x : Fin 64 → ℝ) :
    trialityHadamardEquiv (trialityHadamardEquiv x) = x := by
  change trialityNormalizedHadamard.mulVec (trialityNormalizedHadamard.mulVec x) = x
  rw [Matrix.mulVec_mulVec, triality_normalized_hadamard_square, Matrix.one_mulVec]

lemma trialityOctadAction_inverse_apply (x : Fin 64 → ℝ) :
    trialityOctadAction.symm x = trialityHadamardEquiv (trialitySignEquiv x) := by
  apply trialityOctadAction.injective
  rw [LinearEquiv.apply_symm_apply]
  change x = trialitySignEquiv
    (trialityHadamardEquiv (trialityHadamardEquiv (trialitySignEquiv x)))
  rw [trialityHadamardEquiv_double, trialitySignEquiv_double]

lemma trialityIntegerDiagonal_real (e : Fin 64) :
    (trialityIntegerDiagonal e : ℝ) =
      (if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then (1 : ℝ) else -1) := by
  unfold trialityIntegerDiagonal
  split_ifs <;> simp

lemma cocodeDictionaryAction_octad (h : SpinIndex) (b : TrialityBlocks) (o : Fin 759) :
    (cocodeDictionaryAction h b).2.2.1 o =
      qSign (spinDot h (golayLabelCoefficients (golayOctadLabel o))) •
        trialitySignEquiv (b.2.2.1 o) := by
  funext e
  simp only [cocodeDictionaryAction, Pi.smul_apply, smul_eq_mul, trialityIntegerDiagonal_real]
  let a : ℝ := qSign (spinDot h (golayLabelCoefficients (golayOctadLabel o)))
  let d : ℝ := if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 1 else -1
  change a * d * b.2.2.1 o e = a * (d * b.2.2.1 o e)
  exact mul_assoc _ _ _

lemma trialityRowReflection_cycle (s : Fin 3) :
    trialityRowReflection (trialityCycle.symm (trialityRowReflection s)) = trialityCycle s := by
  revert s
  decide +kernel

lemma trialityCycleAction_inverse_apply (n : ℕ) (v : Fin 3 → Fin n → ℝ)
    (s : Fin 3) (i : Fin n) :
    (trialityCycleAction n).symm v s i = v (trialityCycle s) i := by
  have he : (trialityCycleAction n).symm v = fun s => v (trialityCycle s) := by
    apply (trialityCycleAction n).injective
    rw [LinearEquiv.apply_symm_apply]
    ext t j
    simp only [trialityCycleAction, LinearEquiv.piCongrLeft'_apply, Equiv.apply_symm_apply]
  exact congrArg (fun f => f s i) he

/-- Odd cocode reflection conjugates the full actual dictionary triality to its inverse. -/
theorem cocodeDictionaryAction_triality_inverse (h : SpinIndex) (b : TrialityBlocks) :
    cocodeDictionaryAction h (trialityBlockAction (cocodeDictionaryAction h b)) =
      trialityBlockAction.symm b := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext s p
      simp only [cocodeDictionaryAction, trialityBlockAction, LinearEquiv.prodCongr_apply,
        trialityCycleAction, LinearEquiv.piCongrLeft'_apply, trialityRowReflection_cycle,
        LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
      change b.2.1 (trialityCycle s) p = (trialityCycleAction 276).symm b.2.1 s p
      exact (trialityCycleAction_inverse_apply 276 b.2.1 s p).symm
    · apply Prod.ext
      · funext o
        rw [cocodeDictionaryAction_octad]
        change qSign (spinDot h (golayLabelCoefficients (golayOctadLabel o))) •
          trialitySignEquiv (trialityOctadAction ((cocodeDictionaryAction h b).2.2.1 o)) =
            trialityOctadAction.symm (b.2.2.1 o)
        rw [cocodeDictionaryAction_octad, trialityOctadAction_inverse_apply]
        change _ • trialitySignEquiv (trialitySignEquiv
          (trialityHadamardEquiv (_ • trialitySignEquiv (b.2.2.1 o)))) = _
        rw [trialitySignEquiv_double, map_smul, smul_smul, qSign_sq, one_smul]
      · funext s k
        simp only [cocodeDictionaryAction, trialityBlockAction, LinearEquiv.prodCongr_apply,
          trialityCycleAction, LinearEquiv.piCongrLeft'_apply, trialityRowReflection_cycle,
        LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
        have hs := cocodeXYZScalar_square h
          (finProdFinEquiv.symm k : Fin 2048 × Fin 24).1
          (finProdFinEquiv.symm k : Fin 2048 × Fin 24).2
        change _ * (_ * _) = _
        rw [← mul_assoc, ← pow_two, hs, one_mul]
        change b.2.2.2 (trialityCycle s) k = (trialityCycleAction 49152).symm b.2.2.2 s k
        exact (trialityCycleAction_inverse_apply 49152 b.2.2.2 s k).symm

lemma cocodeQ_square (h : SpinIndex) : cocodeQ h * cocodeQ h = 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · change ofAdd (binaryCocodeEmbedding h) * ofAdd (binaryCocodeEmbedding h) = 1
    apply toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    ext i
    exact ZModModule.add_self _
  · change (1 : Multiplicative (ZMod 2)) * 1 * qCocycle.cocycle _ _ = 1
    rw [one_mul, one_mul]
    apply toAdd.injective
    change qBeta (toAdd (cocodeQ h).base) (toAdd (cocodeQ h).base) = 0
    rw [qBeta_spin_coordinates, cocodeQ_translation, cocodeQ_modulation, spinDot_zero_left]

/-- The actual local odd cocode element inverts the actual extra generator. -/
theorem cocodeQ_conjugates_sExtra_inverse (h : SpinIndex) (hh : h 11 = 1) :
    rhoLocal (inclQ (cocodeQ h)) * sExtra * (rhoLocal (inclQ (cocodeQ h)))⁻¹ = sExtra⁻¹ := by
  have hsq : rhoLocal (inclQ (cocodeQ h)) * rhoLocal (inclQ (cocodeQ h)) = 1 := by
    rw [← map_mul, ← map_mul, cocodeQ_square, map_one, map_one]
  rw [inv_eq_of_mul_eq_one_left hsq]
  apply LinearEquiv.ext
  intro x
  apply trialityBlocksEquiv.injective
  simp only [LinearEquiv.mul_apply, cocodeQ_blocks h hh]
  have ht (y : GriessSpace) : trialityBlocksEquiv (sExtra y) =
      trialityBlockAction (trialityBlocksEquiv y) := by
    simp only [sExtra, griessTriality, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hi (y : GriessSpace) : trialityBlocksEquiv (sExtra⁻¹ y) =
      trialityBlockAction.symm (trialityBlocksEquiv y) := by
    apply trialityBlockAction.injective
    rw [LinearEquiv.apply_symm_apply, ← ht]
    change trialityBlocksEquiv (sExtra (sExtra.symm y)) = trialityBlocksEquiv y
    rw [LinearEquiv.apply_symm_apply]
  rw [ht, hi, cocodeQ_blocks h hh, cocodeDictionaryAction_triality_inverse]

/-- The explicitly source-bound odd singleton cocode {0} inverts triality. -/
theorem singletonCocodeQ_conjugates_sExtra_inverse :
    rhoLocal (inclQ singletonCocodeQ) * sExtra * (rhoLocal (inclQ singletonCocodeQ))⁻¹ =
      sExtra⁻¹ := by
  apply cocodeQ_conjugates_sExtra_inverse
  decide +kernel

/-- The singleton cocode reflection relation inside the actual generated group. -/
theorem singletonCocode_intoGenerated_conjugates_extra :
    qIntoGenerated singletonCocodeQ * extraIntoGenerated *
      (qIntoGenerated singletonCocodeQ)⁻¹ = extraIntoGenerated⁻¹ := by
  apply Subtype.ext
  exact singletonCocodeQ_conjugates_sExtra_inverse

/-- Triality has order dividing three inside the actual generated group. -/
theorem extraIntoGenerated_pow_three : extraIntoGenerated ^ 3 = 1 := by
  apply Subtype.ext
  exact sExtra_pow_three

/-- The two inverse triality factors multiply to triality itself. -/
theorem extraIntoGenerated_inv_mul_inv :
    extraIntoGenerated⁻¹ * extraIntoGenerated⁻¹ = extraIntoGenerated := by
  apply mul_right_cancel (b := extraIntoGenerated * extraIntoGenerated)
  calc
    (extraIntoGenerated⁻¹ * extraIntoGenerated⁻¹) *
        (extraIntoGenerated * extraIntoGenerated) = 1 := by group
    _ = extraIntoGenerated * (extraIntoGenerated * extraIntoGenerated) := by
      simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc]
        using extraIntoGenerated_pow_three.symm

/-- A normal subgroup containing the odd singleton cocode element contains triality. -/
theorem extraIntoGenerated_mem_of_singletonCocode_mem (N : Subgroup ↥G) [hN : N.Normal]
    (hg : qIntoGenerated singletonCocodeQ ∈ N) : extraIntoGenerated ∈ N := by
  have hi := singletonCocode_intoGenerated_conjugates_extra
  have hm : extraIntoGenerated⁻¹ * qIntoGenerated singletonCocodeQ * extraIntoGenerated *
      (qIntoGenerated singletonCocodeQ)⁻¹ = extraIntoGenerated := by
    calc
      _ = extraIntoGenerated⁻¹ * (qIntoGenerated singletonCocodeQ * extraIntoGenerated *
          (qIntoGenerated singletonCocodeQ)⁻¹) := by group
      _ = extraIntoGenerated⁻¹ * extraIntoGenerated⁻¹ := by rw [hi]
      _ = extraIntoGenerated := extraIntoGenerated_inv_mul_inv
  rw [← hm]
  exact N.mul_mem (hN.conj_mem _ hg extraIntoGenerated⁻¹) (N.inv_mem hg)

/-- In particular, any normal subgroup containing embedded Q contains the extra generator. -/
theorem extraIntoGenerated_mem_of_q_range_le (N : Subgroup ↥G) [N.Normal]
    (hQ : qIntoGenerated.range ≤ N) : extraIntoGenerated ∈ N :=
  extraIntoGenerated_mem_of_singletonCocode_mem N (hQ ⟨singletonCocodeQ, rfl⟩)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
