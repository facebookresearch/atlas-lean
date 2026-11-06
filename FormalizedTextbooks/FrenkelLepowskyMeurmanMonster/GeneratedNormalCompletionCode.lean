/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete source code conjugates needed for the normal-subgroup completion. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCrossPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismSigns

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

/-- Every signed source code lift commutes with the actual all-one element Ω. -/
theorem sourceQCode_commute_omega (d : Fin 4096) (ε : ZMod 2) :
    sourceQCode d ε * sourceOmegaQ = sourceOmegaQ * sourceQCode d ε := by
  apply (q_mul_comm_iff _ _).mpr
  rw [qBeta_spin_coordinates, qBeta_spin_coordinates,
    sourceQCode_translation, sourceQCode_modulation,
    sourceOmegaQ_translation, sourceOmegaQ_modulation]
  rw [spinDot_comm (Pi.single 11 1), ← sourceWordTheta_eq_polynomial, sourceWordTheta_dot_omega]
  simp [spinDot]

/-- The source code element commutes with the Ω central-sign pattern in G. -/
theorem sourceGeneratedCode_commute_sign_two (d : Fin 4096) (ε : ZMod 2) :
    sourceGeneratedCode d ε * centralSignIntoGenerated 2 =
      centralSignIntoGenerated 2 * sourceGeneratedCode d ε := by
  rw [← qIntoGenerated_sourceOmegaQ, sourceGeneratedCode, ← map_mul, ← map_mul,
    sourceQCode_commute_omega]

/-- The source code lift commutes with the Y-positive sign pattern as well. -/
theorem sourceGeneratedCode_commute_sign_one (d : Fin 4096) (ε : ZMod 2) :
    sourceGeneratedCode d ε * centralSignIntoGenerated 1 =
      centralSignIntoGenerated 1 * sourceGeneratedCode d ε := by
  have hzero : centralSignIntoGenerated 0 = qIntoGenerated qCentralInvolution := by
    apply Subtype.ext
    exact localCentralGriess_eq_trialityCentralSign.symm
  have hprod : centralSignIntoGenerated 0 * centralSignIntoGenerated 2 =
      centralSignIntoGenerated 1 := by
    apply Subtype.ext
    change trialityCentralSign 0 * trialityCentralSign 2 = trialityCentralSign 1
    rw [← trialityCentralSign_zero_mul_one, ← mul_assoc,
      trialityCentralSign_square, one_mul]
  have hz : sourceGeneratedCode d ε * centralSignIntoGenerated 0 =
      centralSignIntoGenerated 0 * sourceGeneratedCode d ε := by
    rw [hzero]
    exact localIntoGenerated_commute_central (inclQ (sourceQCode d ε))
  rw [← hprod, ← mul_assoc, hz, mul_assoc,
    sourceGeneratedCode_commute_sign_two, ← mul_assoc]

/-- Every source y_d=τ⁻¹x_dτ centralizes the actual central involution.
This proves centralizer membership before any identification with the local H. -/
theorem sourceGeneratedY_commute_central (d : Fin 4096) (ε : ZMod 2) :
    sourceGeneratedY d ε * qIntoGenerated qCentralInvolution =
      qIntoGenerated qCentralInvolution * sourceGeneratedY d ε := by
  have hc := sourceGeneratedCode_commute_sign_one d ε
  have hs : centralSignIntoGenerated 1 =
      extraIntoGenerated * qIntoGenerated qCentralInvolution * extraIntoGenerated⁻¹ := by
    apply Subtype.ext
    exact localCentralGriess_conjugate.symm
  rw [hs] at hc
  change extraIntoGenerated⁻¹ * sourceGeneratedCode d ε * extraIntoGenerated *
      qIntoGenerated qCentralInvolution =
    qIntoGenerated qCentralInvolution *
      (extraIntoGenerated⁻¹ * sourceGeneratedCode d ε * extraIntoGenerated)
  calc
    _ = extraIntoGenerated⁻¹ *
        (sourceGeneratedCode d ε * (extraIntoGenerated * qIntoGenerated qCentralInvolution *
          extraIntoGenerated⁻¹)) * extraIntoGenerated := by group
    _ = extraIntoGenerated⁻¹ *
        ((extraIntoGenerated * qIntoGenerated qCentralInvolution * extraIntoGenerated⁻¹) *
          sourceGeneratedCode d ε) * extraIntoGenerated := by rw [hc]
    _ = _ := by group

/-- Actual source code conjugates belong to the actual centralizer subgroup. -/
theorem sourceGeneratedY_mem_centralizer (d : Fin 4096) (ε : ZMod 2) :
    sourceGeneratedY d ε ∈ Subgroup.centralizer {qIntoGenerated qCentralInvolution} :=
  Subgroup.mem_centralizer_singleton_iff.mpr (sourceGeneratedY_commute_central d ε)

/-- The physical Golay codeword of a source label. -/
def sourceGeneratedSignCode (d : Fin 4096) : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients d), ⟨_, rfl⟩⟩

/-- The actual source code action has the same phase on both pair-short lifts. -/
theorem sourceQCode_pair_phase (d : Fin 4096) (ε : ZMod 2) (s : Fin 2) (p : Fin 276) :
    localShortPhase (localFiberIncl (sourceQCode d ε)) (Sum.inl (s,p)) =
      golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2 := by
  change toAdd (spinConjugation (spinHolomorphIncl (sourceQCode d ε))
    (griessShortQ (Sum.inl (s,p)))).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero, qBeta_spin_coordinates, qBeta_spin_coordinates,
    sourceQCode_translation, sourceQCode_modulation,
    griessPairQ_translation, griessPairQ_modulation]
  rw [spinDot_comm (golayLabelCoefficients d), griessPairSyndrome_dot]
  have ht : spinDot (Pi.single 11 1)
      (sourceCodeThetaPolynomial (golayLabelCoefficients d)) = 0 := by
    rw [spinDot_comm, ← sourceWordTheta_eq_polynomial, sourceWordTheta_dot_omega]
  split_ifs
  · simp [spinDot]
  · rw [ht, add_zero]

/-- The code lift multiplies each short pair coordinate by its encoded character. -/
theorem sourceQCode_short_pair (d : Fin 4096) (ε : ZMod 2)
    (x : GriessShortIndex → ℝ) (s : Fin 2) (p : Fin 276) :
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) x (Sum.inl (s,p)) =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          x (Sum.inl (s,p)) := by
  have hp : griessShortPermutation (localFiberIncl (sourceQCode d ε)).val.2
      (Sum.inl (s,p)) = Sum.inl (s,p) := by
    change griessShortPermutation 1 (Sum.inl (s,p)) = Sum.inl (s,p)
    rw [map_one]; rfl
  have he := localShortOperator_image (localFiberIncl (sourceQCode d ε)) x (Sum.inl (s,p))
  rw [hp, sourceQCode_pair_phase] at he
  exact he

/-- The source code action fixes all diagonal dictionary coordinates. -/
theorem sourceQCode_blocks_diagonal (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode d ε)) x)).1 =
      (trialityBlocksEquiv x).1 := by
  have he := localGriessRepresentation_encode (localFiberIncl (sourceQCode d ε)) x
  have hm := congrArg (fun b : ConwayRawSpace => b.1) he
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).1 =
    conwayMatrixAction 1 (griessConwayEncode x).1 at hm
  rw [map_one] at hm
  funext i
  have hi := congrFun (congrFun hm i) i
  simpa only [griessConwayEncode, dite_true, LinearEquiv.coe_one, id_eq] using hi

/-- The B row of the actual source code action is its physical sign character. -/
theorem sourceQCode_blocks_B (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 1 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 1 p := by
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

/-- The actual triality generator has the prescribed dictionary action. -/
theorem generatedExtra_blocks (x : GriessSpace) :
    trialityBlocksEquiv (sExtra x) = trialityBlockAction (trialityBlocksEquiv x) := by
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- The inverse generator has the inverse dictionary action. -/
theorem generatedExtra_inverse_blocks (x : GriessSpace) :
    trialityBlocksEquiv (sExtra⁻¹ x) = trialityBlockAction.symm (trialityBlocksEquiv x) := by
  apply trialityBlockAction.injective
  rw [LinearEquiv.apply_symm_apply, ← generatedExtra_blocks]
  change trialityBlocksEquiv (sExtra (sExtra.symm x)) = trialityBlocksEquiv x
  rw [LinearEquiv.apply_symm_apply]

/-- Triality fixes the diagonal dictionary block. -/
theorem generatedExtra_blocks_diagonal (x : GriessSpace) :
    (trialityBlocksEquiv (sExtra x)).1 = (trialityBlocksEquiv x).1 := by
  rw [generatedExtra_blocks]
  rfl

/-- Inverse triality fixes the diagonal dictionary block. -/
theorem generatedExtra_inverse_blocks_diagonal (x : GriessSpace) :
    (trialityBlocksEquiv (sExtra⁻¹ x)).1 = (trialityBlocksEquiv x).1 := by
  rw [generatedExtra_inverse_blocks]
  rfl

/-- Inverse triality takes the A coordinate from the B row. -/
theorem generatedExtra_inverse_blocks_A (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra⁻¹ x)).2.1 0 p = (trialityBlocksEquiv x).2.1 1 p := by
  rw [generatedExtra_inverse_blocks]
  change (trialityCycleAction 276).symm (trialityBlocksEquiv x).2.1 0 p = _
  rw [trialityCycleAction_inverse_apply]
  rfl

/-- Triality takes the B coordinate from the A row. -/
theorem generatedExtra_blocks_B (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra x)).2.1 1 p = (trialityBlocksEquiv x).2.1 0 p := by
  rw [generatedExtra_blocks]
  change trialityCycleAction 276 (trialityBlocksEquiv x).2.1 1 p = _
  simp only [trialityCycleAction, LinearEquiv.piCongrLeft'_apply]
  rfl

/-- The actual source y_d fixes the diagonal matrix entries. -/
theorem sourceGeneratedY_blocks_diagonal (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    (trialityBlocksEquiv ((sourceGeneratedY d ε).val x)).1 = (trialityBlocksEquiv x).1 := by
  change (trialityBlocksEquiv
    (sExtra⁻¹ (rhoLocal (inclQ (sourceQCode d ε)) (sExtra x)))).1 = _
  rw [generatedExtra_inverse_blocks_diagonal, sourceQCode_blocks_diagonal,
    generatedExtra_blocks_diagonal]

/-- The actual source y_d scales A by the physical Golay pair character. -/
theorem sourceGeneratedY_blocks_A (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace)
    (p : Fin 276) :
    (trialityBlocksEquiv ((sourceGeneratedY d ε).val x)).2.1 0 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 0 p := by
  change (trialityBlocksEquiv
    (sExtra⁻¹ (rhoLocal (inclQ (sourceQCode d ε)) (sExtra x)))).2.1 0 p = _
  rw [generatedExtra_inverse_blocks_A, sourceQCode_blocks_B, generatedExtra_blocks_B]

/-- Code signs act on physical matrix entries by the two-coordinate character. -/
theorem sourceGeneratedSign_matrix_apply (d : Fin 4096)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (i j : Fin 24) :
    conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d)) a i j =
      qSign (golayEncoder (golayLabelCoefficients d) i +
        golayEncoder (golayLabelCoefficients d) j) * a i j := by
  rw [← Matrix.toBilin'_single
    (conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d)) a) i j,
    conwayMatrixAction_pairing]
  have hi : (golaySignIsometry (sourceGeneratedSignCode d)).val.symm (Pi.single i 1) =
      qSign (golayEncoder (golayLabelCoefficients d) i) • Pi.single i 1 := by
    ext k
    change qSign (golayEncoder (golayLabelCoefficients d) k) *
      (Pi.single i (1 : ℝ) : Fin 24 → ℝ) k = _
    by_cases hk : i = k
    · subst k; simp
    · simp [hk]
  have hj : (golaySignIsometry (sourceGeneratedSignCode d)).val.symm (Pi.single j 1) =
      qSign (golayEncoder (golayLabelCoefficients d) j) • Pi.single j 1 := by
    ext k
    change qSign (golayEncoder (golayLabelCoefficients d) k) *
      (Pi.single j (1 : ℝ) : Fin 24 → ℝ) k = _
    by_cases hk : j = k
    · subst k; simp
    · simp [hk]
  rw [hi, hj]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.toBilin'_single, qSign_add]
  ring

/-- The entire A matrix block of the actual y_d is the actual Golay sign action.
The local membership and quotient projection are separate consequences of the
full centralizer identification and the matrix-action kernel. -/
theorem sourceGeneratedY_matrix (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    (griessConwayEncode ((sourceGeneratedY d ε).val x)).1 =
      conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d))
        (griessConwayEncode x).1 := by
  ext i j
  rw [sourceGeneratedSign_matrix_apply]
  by_cases hij : i = j
  · subst j
    simp only [griessConwayEncode, dite_true, sourceGeneratedY_blocks_diagonal,
      CharTwo.add_self_eq_zero, qSign_zero, one_mul]
  · have hp : golayEncoder (golayLabelCoefficients d)
        (griessCoordinatePair (griessPairIndex i j hij)).1 +
        golayEncoder (golayLabelCoefficients d)
          (griessCoordinatePair (griessPairIndex i j hij)).2 =
        golayEncoder (golayLabelCoefficients d) i + golayEncoder (golayLabelCoefficients d) j := by
      rw [griessPairIndex_coordinates]
      split_ifs
      · rfl
      · exact add_comm _ _
    simp only [griessConwayEncode, hij, dite_false]
    rw [sourceGeneratedY_blocks_A, hp]

/-- Every normal subgroup containing embedded Q contains every actual source y_d. -/
theorem sourceGeneratedY_mem_of_q_range_le (N : Subgroup ↥G) [hN : N.Normal]
    (hQ : qIntoGenerated.range ≤ N) (d : Fin 4096) (ε : ZMod 2) :
    sourceGeneratedY d ε ∈ N := by
  exact hN.conj_mem (sourceGeneratedCode d ε) (hQ ⟨sourceQCode d ε, rfl⟩)
    extraIntoGenerated⁻¹

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
