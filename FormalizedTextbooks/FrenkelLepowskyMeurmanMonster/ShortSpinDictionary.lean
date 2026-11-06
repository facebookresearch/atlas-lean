/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source code-generator lifts and their spin dictionary coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

open scoped BigOperators

/-- The cocode adjustment in the source modified-code frame. -/
def sourceCodeThetaCoefficients (j : Fin 12) (k : Fin 12) : ℤ :=
  if (parkerBasisThetaMasks j).testBit k.val then 1 else 0

/-- Actual lattice lift of a published code generator, obtained from its
certified source frame column and the explicit cocode correction. -/
noncomputable def leechSourceCodeLift (j : Fin 12) : leechIntegral :=
  leechSourceFrameLift (Fin.castAdd 12 j) -
    ∑ k, sourceCodeThetaCoefficients j k • leechCocodeLift (golayCocodeInteger k)

/-- The code lift has the physical vector specified in Seysen Theorem 6.1. -/
theorem leechSourceCodeLift_vector (j : Fin 12) :
    (leechSourceCodeLift j).val = leechSourceCodeVector j := by
  funext i
  have hframe := congrFun (leechSourceFrameLift_vector (Fin.castAdd 12 j)) i
  simp only [Matrix.col_apply, leechSourceFrameVectors, Fin.val_castAdd,
    j.isLt, dite_true] at hframe
  change (leechSourceFrameLift (Fin.castAdd 12 j)).val i -
    (∑ k, sourceCodeThetaCoefficients j k • leechCocodeLift (golayCocodeInteger k)).val i = _
  rw [hframe]
  have hsum : (∑ k, sourceCodeThetaCoefficients j k •
      leechCocodeLift (golayCocodeInteger k)).val i =
      ∑ k, if (parkerBasisThetaMasks j).testBit k.val then
        leechSourceCocodeVector k i else 0 := by
    change (leechIntegral.subtype (∑ k, sourceCodeThetaCoefficients j k •
      leechCocodeLift (golayCocodeInteger k))) i = _
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      sourceCodeThetaCoefficients, Submodule.subtype_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [leechCocodeLift_basis, leechSourceFrameLift_vector]
    simp only [Matrix.col_apply, leechSourceFrameVectors, Fin.val_natAdd]
    have hn : ¬ 12 + k.val < 12 := by omega
    simp only [hn, dite_false]
    split_ifs <;> simp
  rw [hsum]
  exact add_sub_cancel_right _ _

/-- The Parker theta correction as a binary cocode vector. -/
def sourceCodeTheta (j : Fin 12) (k : Fin 12) : ZMod 2 :=
  if (parkerBasisThetaMasks j).testBit k.val then 1 else 0

/-- The actual source code lift has precisely the code and theta coordinates
used by the spin dictionary. -/
theorem leechSourceCodeLift_hyperbolic (j : Fin 12) :
    leechHyperbolicCoordinates (leechReduction (leechSourceCodeLift j)) =
      Pi.single (Fin.castAdd 12 j) 1 + binaryCocodeEmbedding (sourceCodeTheta j) := by
  rw [leechSourceCodeLift, map_sub, map_sub, leechSourceFrameLift_hyperbolic,
    map_sum, map_sum]
  have hs : (∑ k, leechHyperbolicCoordinates
      (leechReduction (sourceCodeThetaCoefficients j k •
        leechCocodeLift (golayCocodeInteger k)))) =
      binaryCocodeEmbedding (sourceCodeTheta j) := by
    simp only [map_zsmul]
    simp_rw [leechCocodeLift_basis_hyperbolic, ← binaryCocodeEmbedding_basis]
    ext i
    refine Fin.addCases (m := 12) (n := 12) (fun k => ?_) (fun k => ?_) i
    · simp only [Finset.sum_apply, Pi.smul_apply, binaryCocodeEmbedding_left,
        smul_zero, Finset.sum_const_zero]
    · simp only [Finset.sum_apply, Pi.smul_apply, binaryCocodeEmbedding_right]
      simp [sourceCodeThetaCoefficients, sourceCodeTheta, Pi.single_apply]
  rw [hs]
  ext i
  have hn : ∀ a : ZMod 2, -a = a := by decide +kernel
  simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, hn]

/-- Twice the physical characteristic vector of a Golay word. -/
def leechTwiceCodeWordVector (d : Fin 4096) (i : Fin 24) : ℤ :=
  2 * if (golayEncodedMask d.val).testBit i.val then 1 else 0

/-- Doubly even Golay weights give an actual integral Leech vector. -/
theorem leechTwiceCodeWordVector_mem (d : Fin 4096) :
    leechTwiceCodeWordVector d ∈ leechIntegral := by
  rw [mem_leechIntegral_iff_source]
  refine ⟨0, Or.inl rfl, golayEncoder (golayLabelCoefficients d), ⟨_, rfl⟩, ?_, ?_⟩
  · intro i
    rw [golayLabelEncoder_match]
    simp [leechTwiceCodeWordVector]
  · have hs : (∑ i, leechTwiceCodeWordVector d i) =
        2 * (golayMaskWeight (golayEncodedMask d.val) : ℤ) := by
      simp only [leechTwiceCodeWordVector, golayMaskWeight, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> norm_num
    rw [hs]
    have hw := golayEncodedMask_weights d
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw | hw | hw | hw <;> rw [hw] <;> decide +kernel

noncomputable def leechTwiceCodeWordLift (d : Fin 4096) : leechIntegral :=
  ⟨leechTwiceCodeWordVector d, leechTwiceCodeWordVector_mem d⟩

/-- The normalized source representative λ_d, using the complement when the
word has weight four modulo eight, as in Seysen Theorem 6.1. -/
def leechSourceCodeWordVector (d : Fin 4096) (i : Fin 24) : ℤ :=
  if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then
    2 * if (golayEncodedMask d.val).testBit i.val then 1 else 0
  else 2 * (1 - if (golayEncodedMask d.val).testBit i.val then 1 else 0)

noncomputable def leechSourceCodeWordLift (d : Fin 4096) : leechIntegral :=
  if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then leechTwiceCodeWordLift d
  else leechTwiceCodeWordLift 2048 - leechTwiceCodeWordLift d

/-- The normalized lift is an actual lattice element with the source vector. -/
theorem leechSourceCodeWordLift_vector (d : Fin 4096) :
    (leechSourceCodeWordLift d).val = leechSourceCodeWordVector d := by
  funext i
  have hΩ : (golayEncodedMask 2048).testBit i.val = true := by
    fin_cases i <;> decide
  by_cases h : golayMaskWeight (golayEncodedMask d.val) % 8 = 0
  · simp only [leechSourceCodeWordLift, leechSourceCodeWordVector, h, ite_true]
    rfl
  · simp only [leechSourceCodeWordLift, leechSourceCodeWordVector, h, ite_false]
    simp only [Submodule.coe_sub, Pi.sub_apply, leechTwiceCodeWordLift,
      leechTwiceCodeWordVector]
    change 2 * (if (golayEncodedMask 2048).testBit i.val then 1 else 0) -
        2 * (if (golayEncodedMask d.val).testBit i.val then 1 else 0) = _
    rw [hΩ]
    simp only [ite_true]
    ring

/-- The published code-generator label. -/
def sourceCodeGeneratorLabel (j : Fin 12) : Fin 4096 :=
  ⟨2 ^ j.val, by fin_cases j <;> decide⟩

set_option maxHeartbeats 1000000 in
-- Compare the 12 generator representatives in the 24 physical coordinates.
theorem leechSourceCodeWordVector_generator : ∀ j : Fin 12,
    leechSourceCodeWordVector (sourceCodeGeneratorLabel j) = leechSourceCodeVector j := by
  unfold leechSourceCodeWordVector sourceCodeGeneratorLabel leechSourceCodeVector
  decide +kernel

/-- The arbitrary-word source lift extends the certified source-generator lift. -/
theorem leechSourceCodeWordLift_generator (j : Fin 12) :
    leechSourceCodeWordLift (sourceCodeGeneratorLabel j) = leechSourceCodeLift j := by
  apply Subtype.ext
  rw [leechSourceCodeWordLift_vector, leechSourceCodeLift_vector,
    leechSourceCodeWordVector_generator]

/-- Generator case of the full source code-word coordinate dictionary. -/
theorem leechSourceCodeWordLift_generator_hyperbolic (j : Fin 12) :
    leechHyperbolicCoordinates (leechReduction
      (leechSourceCodeWordLift (sourceCodeGeneratorLabel j))) =
      Pi.single (Fin.castAdd 12 j) 1 + binaryCocodeEmbedding (sourceCodeTheta j) := by
  rw [leechSourceCodeWordLift_generator, leechSourceCodeLift_hyperbolic]

/-- The negative positions in an octad as integer cocode coefficients. -/
def griessOctadNegativeInteger (d : Fin 759) (e : Fin 64) (i : Fin 24) : ℤ :=
  if (griessOctadSignMask d e).testBit i.val then 1 else 0

/-- The all-one twice-code lift is the actual all-one source-frame column. -/
theorem leechTwiceCodeWordLift_omega :
    leechTwiceCodeWordLift 2048 = leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12)) := by
  apply Subtype.ext
  rw [leechSourceFrameLift_omega_vector]
  funext i
  change 2 * (if (golayEncodedMask 2048).testBit i.val then 1 else 0) = 2
  have h : (golayEncodedMask 2048).testBit i.val = true := by fin_cases i <;> decide
  simp [h]

/-- Signed octads decompose into their code lift, negative cocode lift, and
an explicit multiple of the all-one lift. -/
theorem griessOctad_source_lift (d : Fin 759) (e : Fin 64) :
    griessShortLatticeVector (Sum.inr (Sum.inl (d, e))) =
      leechTwiceCodeWordLift (golayOctadLabel d) +
        leechCocodeLift (griessOctadNegativeInteger d e) -
          ((trialityBitWeight8 (trialityEvenMask e) / 2 : ℕ) : ℤ) •
            leechTwiceCodeWordLift 2048 := by
  apply Subtype.ext
  funext i
  have hs : (∑ k, griessOctadNegativeInteger d e k) =
      (trialityBitWeight8 (trialityEvenMask e) : ℤ) := by
    have h := griessOctadSignMask_weight d e
    simpa only [golayMaskWeight, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, griessOctadNegativeInteger] using congrArg (fun n : ℕ => (n : ℤ)) h
  have he := trialityEvenMask_even e
  have hn : (((trialityBitWeight8 (trialityEvenMask e) / 2 : ℕ) : ℤ) * 2) =
      (trialityBitWeight8 (trialityEvenMask e) : ℤ) := by
    exact_mod_cast Nat.div_mul_cancel he
  rw [leechTwiceCodeWordLift_omega]
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, leechTwiceCodeWordLift,
    leechTwiceCodeWordVector, leechCocodeLift, LinearMap.coe_mk, AddHom.coe_mk,
    griessShortLatticeVector, griessShortIntegral,
    leechSourceFrameLift_omega_vector]
  simp only [leechCocodeVector]
  rw [hs]
  simp only [griessOctadNegativeInteger]
  rw [hn]
  have hi := griessOctadSignMask_subset d e i
  split_ifs <;> simp_all
  ring

/-- Odd shortest vectors decompose into the singleton cocode lift, twice their
Golay word, and the all-one correction at the distinguished coordinate. -/
theorem griessOdd_source_lift (d : Fin 2048) (j : Fin 24) :
    griessShortLatticeVector (Sum.inr (Sum.inr (d, j))) =
      leechCocodeLift (Pi.single j 1) - leechTwiceCodeWordLift ⟨d.val, by omega⟩ +
        (if (golayEncodedMask d.val).testBit j.val then (1 : ℤ) else 0) •
          (leechTwiceCodeWordLift 2048 - (2 : ℤ) • leechCocodeLift (Pi.single j 1)) := by
  apply Subtype.ext
  funext i
  rw [leechTwiceCodeWordLift_omega]
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, leechCocodeLift, LinearMap.coe_mk, AddHom.coe_mk,
    leechTwiceCodeWordLift, leechTwiceCodeWordVector, griessShortLatticeVector,
    griessShortIntegral,
    leechSourceFrameLift_omega_vector]
  simp only [leechCocodeVector, Pi.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · subst i
    simp only [ite_true]
    split_ifs <;> norm_num
  · simp only [hij, ite_false]
    split_ifs <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
