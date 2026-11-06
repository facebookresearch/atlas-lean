/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerMatrixActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorIntegerFixation

/-! Canonical compact-axis full-fixer assembly. All new proof bodies are uncompiled drafts.
Every full preferred mask, central phase and signed tensor coordinate remains certified. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Complete canonical and original final matrices agree by the incoming M and C formulas. -/
theorem generatedTenth_source_compact_canonical_matrix :
    (griessConwayEncode generatedTenthSourceCompactAxis).1 =
      (griessConwayEncode generatedTenthAxis).1 := by
  rw [generatedTenth_source_compact_final_packet_actual, generatedTenth_matrix]
  change generatedAxisGlobalRawTrialityMatrix generatedTenthSourceCompactIncomingPacket =
    generatedAxisGlobalRawTrialityMatrix generatedAxisGlobalFifthRoot02Packet
  funext i j
  simp only [generatedAxisGlobalRawTrialityMatrix,
    generatedTenth_source_compact_incoming_matrix, generatedTenth_source_compact_incoming_short]

/-- Both genuine spatial maps fix the entire canonical final matrix without a finite premise. -/
theorem generatedTenth_source_compact_canonical_matrix_fix (g : Fin 2) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis)).1 =
        (griessConwayEncode generatedTenthSourceCompactAxis).1 := by
  rw [generatedFourth_local_matrix, generatedTenth_source_compact_canonical_matrix]
  exact generatedTenth_two_fixer_matrix_action_fix g

private theorem C_fiber_eq_tensor_fiber (g : Fin 2) :
    generatedTenthTwoFixerCFiber g = generatedTenthTwoFixerTensorFiber g := by
  fin_cases g <;> rfl

/-- Unchanged complete support certificates bind the canonical C field, including its zeros. -/
theorem generatedTenth_source_compact_canonical_C_fix (g : Fin 2)
    (destination : Fin 98280 → Fin 98280) (phase : Fin 98280 → ZMod 2)
    (hsource : GeneratedTenthSourceCompactCanonicalCInputCondition)
    (hsupport : GeneratedTenthTwoFixerCSupportCondition g destination phase) :
    localShortRepresentation (generatedTenthTwoFixerTensorFiber g)
      (griessConwayEncode generatedTenthSourceCompactAxis).2.1 =
        (griessConwayEncode generatedTenthSourceCompactAxis).2.1 := by
  rw [← C_fiber_eq_tensor_fiber g]
  apply generatedNinth_lower_spin_short_fixer_of_nonzero_sources
  intro r hr
  have hn : generatedTenthFinalShortPackedCacheCoefficient r ≠ 0 := by
    intro hz
    have hh := hsource r
    rw [hz, Int.cast_zero] at hh
    apply hr
    linarith
  let a := generatedNinthLowerSpinShortAddress r
  have hp := hsupport a (by
    simpa only [a, generatedNinth_lower_spin_short_index_address] using hn)
  have hd := generatedTenth_two_fixer_c_destination_actual g destination phase a hp
  have ho := monsterNortonShortOperator_of_Q_image (generatedTenthTwoFixerCFiber g)
    (generatedNinthLowerSpinShortIndex a)
    (generatedNinthLowerSpinShortIndex (destination a)) (phase a)
    (generatedTenth_two_fixer_c_image g destination phase a hp)
    (griessConwayEncode generatedTenthSourceCompactAxis).2.1
  have hz := congrArg (fun z : ℤ => (z : ℝ)) hp.2.2
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hz
  rw [← hsource (generatedNinthLowerSpinShortIndex a),
    ← hsource (generatedNinthLowerSpinShortIndex (destination a))] at hz
  simp only [a, generatedNinth_lower_spin_short_index_address] at hd ho hz
  change localShortOperator (generatedTenthTwoFixerCFiber g)
    (griessConwayEncode generatedTenthSourceCompactAxis).2.1
      (griessShortPermutation (generatedTenthTwoFixerCFiber g).val.2 r) = _
  rw [hd, ho]
  nlinarith

/-- The whole tensor input is bound at arbitrary genuine spin labels, not chosen-source spins. -/
theorem generatedTenth_source_compact_canonical_tensor_input
    (hinput : GeneratedTenthSourceCompactCanonicalTInputCondition)
    (t : SpinIndex) (j : Fin 24) :
    512 * Real.sqrt 2 * (griessConwayEncode generatedTenthSourceCompactAxis).2.2 t j =
      (generatedTenthTwoFixerTensorInput (nortonUIntegerLabel t) j : ℝ) := by
  obtain ⟨n, rfl⟩ := golayLabelCoefficients_bijective.2 t
  rw [nortonUIntegerLabel_coeff]
  exact hinput n j

/-- The unchanged complete integer tensor circuit fixes the full canonical tensor field. -/
theorem generatedTenth_source_compact_canonical_T_fix
    (hinput : GeneratedTenthSourceCompactCanonicalTInputCondition)
    (hphysical : GeneratedTenthTwoFixerTensorPhysicalCondition)
    (hstart : GeneratedTenthTwoFixerTensorStartCondition)
    (hpairs : GeneratedTenthTwoFixerTensorPairCondition)
    (hfinish : GeneratedTenthTwoFixerTensorFinishCondition) (g : Fin 2) :
    localTensorRepresentation (generatedTenthTwoFixerTensorFiber g)
      (griessConwayEncode generatedTenthSourceCompactAxis).2.2 =
        (griessConwayEncode generatedTenthSourceCompactAxis).2.2 := by
  let c : ℝ := 512 * Real.sqrt 2
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hI : c • (griessConwayEncode generatedTenthSourceCompactAxis).2.2 =
      (fun t j => (generatedTenthTwoFixerTensorInput (nortonUIntegerLabel t) j : ℝ)) := by
    ext t j
    exact generatedTenth_source_compact_canonical_tensor_input hinput t j
  have hi := generatedTenth_two_fixer_tensor_integer_fix hphysical hstart hpairs hfinish g
  have hs : c • localTensorRepresentation (generatedTenthTwoFixerTensorFiber g)
      (griessConwayEncode generatedTenthSourceCompactAxis).2.2 =
        c • (griessConwayEncode generatedTenthSourceCompactAxis).2.2 := by
    rw [← map_smul, hI, hi]
  funext t j
  have h := congrFun (congrFun hs t) j
  simp only [Pi.smul_apply, smul_eq_mul] at h
  exact mul_left_cancel₀ hc h

/-- Full C and T fixation plus the proved matrix equality gives genuine whole-axis fixation. -/
theorem generatedTenth_source_compact_canonical_axis_fix_of_components (g : Fin 2)
    (hC : localShortRepresentation (generatedTenthTwoFixerTensorFiber g)
      (griessConwayEncode generatedTenthSourceCompactAxis).2.1 =
        (griessConwayEncode generatedTenthSourceCompactAxis).2.1)
    (hT : localTensorRepresentation (generatedTenthTwoFixerTensorFiber g)
      (griessConwayEncode generatedTenthSourceCompactAxis).2.2 =
        (griessConwayEncode generatedTenthSourceCompactAxis).2.2) :
    rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis := by
  have hshort : (griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
        generatedTenthSourceCompactAxis)).2.1 =
          (griessConwayEncode generatedTenthSourceCompactAxis).2.1 := by
    rw [generatedFourth_local_short]
    exact hC
  have htensor : (griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
        generatedTenthSourceCompactAxis)).2.2 =
          (griessConwayEncode generatedTenthSourceCompactAxis).2.2 := by
    rw [generatedFourth_local_tensor]
    exact hT
  have he := Prod.ext (generatedTenth_source_compact_canonical_matrix_fix g)
    (Prod.ext hshort htensor)
  have hd := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode] using hd

/-- The two literal fibers fix the canonical whole axis under the unchanged full certificates. -/
theorem generatedTenth_source_compact_canonical_two_fixers
    (destination : Fin 2 → Fin 98280 → Fin 98280)
    (phase : Fin 2 → Fin 98280 → ZMod 2)
    (hC : GeneratedTenthSourceCompactCanonicalCInputCondition)
    (hT : GeneratedTenthSourceCompactCanonicalTInputCondition)
    (hsupport : ∀ g, GeneratedTenthTwoFixerCSupportCondition g (destination g) (phase g))
    (hphysical : GeneratedTenthTwoFixerTensorPhysicalCondition)
    (hstart : GeneratedTenthTwoFixerTensorStartCondition)
    (hpairs : GeneratedTenthTwoFixerTensorPairCondition)
    (hfinish : GeneratedTenthTwoFixerTensorFinishCondition) (g : Fin 2) :
    rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis := by
  exact generatedTenth_source_compact_canonical_axis_fix_of_components g
    (generatedTenth_source_compact_canonical_C_fix g (destination g) (phase g) hC (hsupport g))
    (generatedTenth_source_compact_canonical_T_fix hT hphysical hstart hpairs hfinish g)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
