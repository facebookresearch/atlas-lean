/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The concrete monomial operators obey the exact source code and cocode conjugation laws. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCrossPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The full source theta difference equals the derivative of the checked compact phase. -/
theorem monsterSourcePermutation_difference_gradient (k : Fin 2) (a b : SpinIndex) :
    monsterSourcePermutationThetaDifference k a b =
      spinDot (monsterMonomialGradient (monsterSourcePermutationPhaseData k) a) b := by
  rw [monsterSourcePermutationPhaseData_eq]
  exact (monsterSourcePermutationThetaBilinear_apply k a b).symm.trans
    ((LinearMap.congr_fun₂ (monsterSourcePermutationTheta_bilinear k) a b).trans
      (monsterMonomialGradientBilinear_apply (monsterSourcePermutationPhaseMatrix k) a b))

/-- Theta transforms by exactly the phase shear required by the source Parker lift. -/
theorem monsterSourcePermutation_theta_transport (k : Fin 2) (a : SpinIndex) :
    monsterMonomialPullback (monsterSourcePermutationCode k).symm
      (sourceCodeThetaPolynomial a +
        monsterMonomialGradient (monsterSourcePermutationPhaseData k) a) =
      sourceCodeThetaPolynomial (monsterSourcePermutationCode k a) := by
  ext j
  have h := monsterSourcePermutation_difference_gradient k a
    ((monsterSourcePermutationCode k).symm (Pi.single j 1))
  unfold monsterSourcePermutationThetaDifference at h
  rw [LinearEquiv.apply_symm_apply, spinDot_single_right] at h
  change spinDot (sourceCodeThetaPolynomial a +
    monsterMonomialGradient (monsterSourcePermutationPhaseData k) a)
      ((monsterSourcePermutationCode k).symm (Pi.single j 1)) = _
  rw [spinDot_add_left]
  have hz := CharTwo.add_self_eq_zero
    (spinDot (sourceCodeThetaPolynomial a)
      ((monsterSourcePermutationCode k).symm (Pi.single j 1)))
  linear_combination -h + hz

/-- The source quadratic cochain has zero self-polarization. -/
theorem monsterSourcePermutation_difference_self (k : Fin 2) (a : SpinIndex) :
    monsterSourcePermutationThetaDifference k a a = 0 := by
  have h := monsterSourcePermutationPhase_polarization k a a
  have ha : a + a = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (a i)
  rw [ha, CharTwo.add_self_eq_zero, zero_add] at h
  have hz : monsterSourcePermutationPhase k 0 = 0 := by
    simp [monsterSourcePermutationPhase]
  exact h.symm.trans hz

/-- A genuine permuted code label has the same quarter-weight phase. -/
theorem monsterSourcePermutation_quarter_weight (k : Fin 2) (d e : Fin 4096)
    (he : golayLabelCoefficients e = monsterSourcePermutationCode k (golayLabelCoefficients d)) :
    ((golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) : ZMod 2) =
      ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) := by
  have h := monsterSourcePermutation_difference_self k (golayLabelCoefficients d)
  unfold monsterSourcePermutationThetaDifference at h
  rw [← he, sourceCodeThetaPolynomial_self_dot, sourceCodeThetaPolynomial_self_dot] at h
  exact (add_eq_zero_iff_eq_neg.mp h).trans (CharTwo.neg_eq _)

/-- Equality in actual Q follows from its three genuine Schrödinger coordinates. -/
theorem monsterMonomialQ_ext (q r : Q)
    (ha : spinTranslation q = spinTranslation r) (hb : spinModulation q = spinModulation r)
    (hc : toAdd q.coeff = toAdd r.coeff) : q = r := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    ext i
    refine Fin.addCases (m := 12) (n := 12) ?_ ?_ i
    · intro j
      exact congrFun ha j
    · intro j
      exact congrFun hb j
  · exact toAdd.injective hc

/-- The source monomial image has the actual permuted translation coordinates. -/
theorem monsterSourcePermutationImage_translation (k : Fin 2) (q : Q) :
    spinTranslation (monsterSourcePermutationImage k q) =
      monsterSourcePermutationCode k (spinTranslation q) := by
  rw [monsterSourcePermutationImage, monsterMonomialPermutationImage_translation,
    monsterMonomialDiagonalImage_translation]

/-- The genuine permutation operator pulls back each modulation coordinate. -/
theorem monsterMonomialPermutationImage_modulation
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) :
    spinModulation (monsterMonomialPermutationImage P q) =
      monsterMonomialPullback P.symm (spinModulation q) := by
  ext i
  exact Fin.append_right _ _ i

/-- The signed diagonal adds the concrete derivative to each modulation coordinate. -/
theorem monsterMonomialDiagonalImage_modulation (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) :
    spinModulation (monsterMonomialDiagonalImage M q) =
      spinModulation q + monsterMonomialGradient M (spinTranslation q) := by
  ext i
  exact Fin.append_right _ _ i

/-- The source monomial image has the actual pulled-back, sheared modulation coordinates. -/
theorem monsterSourcePermutationImage_modulation (k : Fin 2) (q : Q) :
    spinModulation (monsterSourcePermutationImage k q) =
      monsterMonomialPullback (monsterSourcePermutationCode k).symm
        (spinModulation q + monsterMonomialGradient (monsterSourcePermutationPhaseData k)
          (spinTranslation q)) := by
  rw [monsterSourcePermutationImage, monsterMonomialPermutationImage_modulation,
    monsterMonomialDiagonalImage_modulation]

/-- The genuine central coefficient changes by precisely the source quadratic phase. -/
theorem monsterSourcePermutationImage_coefficient (k : Fin 2) (q : Q) :
    toAdd (monsterSourcePermutationImage k q).coeff = toAdd q.coeff +
      monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) (spinTranslation q) := rfl

/-- The actual signed source code has its prescribed quarter-weight central coefficient. -/
theorem monsterSourceQCode_coefficient (d : Fin 4096) (ε : ZMod 2) :
    toAdd (sourceQCode d ε).coeff = ε +
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := rfl

/-- The explicit operator has the source signed-code conjugation law on every codeword. -/
theorem monsterSourcePermutationImage_code (k : Fin 2) (d e : Fin 4096) (ε : ZMod 2)
    (he : golayLabelCoefficients e = monsterSourcePermutationCode k (golayLabelCoefficients d)) :
    monsterSourcePermutationImage k (sourceQCode d ε) =
      sourceQCode e (ε + monsterSourcePermutationPhase k (golayLabelCoefficients d)) := by
  apply monsterMonomialQ_ext
  · rw [monsterSourcePermutationImage_translation, sourceQCode_translation,
      sourceQCode_translation, he]
  · rw [monsterSourcePermutationImage_modulation, sourceQCode_translation,
      sourceQCode_modulation, monsterSourcePermutation_theta_transport,
      sourceQCode_modulation, he]
  · rw [monsterSourcePermutationImage_coefficient, monsterSourceQCode_coefficient,
      monsterSourceQCode_coefficient, sourceQCode_translation,
      monsterSourcePermutationPhaseData_eq,
      ← monsterSourcePermutation_quarter_weight k d e he]
    change (ε + (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)) +
      monsterSourcePermutationPhase k (golayLabelCoefficients d) =
        (ε + monsterSourcePermutationPhase k (golayLabelCoefficients d)) +
          (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)
    abel

/-- The exact source monomial sends every positive cocode lift to its pulled-back cocode. -/
theorem monsterSourcePermutationImage_cocode (k : Fin 2) (δ : SpinIndex) :
    monsterSourcePermutationImage k (sourceQCocode δ) =
      sourceQCocode (monsterMonomialPullback (monsterSourcePermutationCode k).symm δ) := by
  apply monsterMonomialQ_ext
  · rw [monsterSourcePermutationImage_translation, sourceQCocode_translation,
      sourceQCocode_translation, map_zero]
  · rw [monsterSourcePermutationImage_modulation, sourceQCocode_translation,
      sourceQCocode_modulation, sourceQCocode_modulation]
    have hz : monsterMonomialGradient (monsterSourcePermutationPhaseData k) (0 : SpinIndex) = 0 :=
      by
      ext i
      simp [monsterMonomialGradient]
    rw [hz, add_zero]
  · rw [monsterSourcePermutationImage_coefficient, sourceQCocode_translation]
    change 0 + monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) 0 = 0
    simp [monsterMonomialQuadratic]

/-- The actual local source monomial conjugates genuine Q elements by the proved source formula. -/
theorem monsterSourcePermutationLocal_conjugation (k : Fin 2) (q : Q) :
    monsterSourcePermutationLocal k * inclQ q * (monsterSourcePermutationLocal k)⁻¹ =
      inclQ (monsterSourcePermutationImage k q) := by
  have h := localFiberIncl_conjugate (monsterSourcePermutationFiber k) q
  change localFiberIncl (spinConjugation (monsterSourcePermutationSpin k) q) =
    monsterSourcePermutationFiber k * localFiberIncl q * (monsterSourcePermutationFiber k)⁻¹ at h
  rw [monsterSourcePermutationSpin_conjugation] at h
  have hquot := congrArg (QuotientGroup.mk' localDiagonalSubgroup) h
  rw [map_mul, map_mul, map_inv] at hquot
  exact hquot.symm

/-- The source conjugation formula holds in the named generated group G. -/
theorem monsterSourcePermutationGenerated_conjugation (k : Fin 2) (q : Q) :
    monsterSourcePermutationGenerated k * qIntoGenerated q *
      (monsterSourcePermutationGenerated k)⁻¹ =
        qIntoGenerated (monsterSourcePermutationImage k q) := by
  unfold monsterSourcePermutationGenerated qIntoGenerated
  simp only [MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, monsterSourcePermutationLocal_conjugation]

/-- In the named G, every signed source code obeys the precise standard Parker action. -/
theorem monsterSourcePermutationGenerated_code (k : Fin 2) (d e : Fin 4096) (ε : ZMod 2)
    (he : golayLabelCoefficients e = monsterSourcePermutationCode k (golayLabelCoefficients d)) :
    monsterSourcePermutationGenerated k * sourceGeneratedCode d ε *
      (monsterSourcePermutationGenerated k)⁻¹ =
      sourceGeneratedCode e (ε + monsterSourcePermutationPhase k (golayLabelCoefficients d)) :=
    by
  rw [sourceGeneratedCode, monsterSourcePermutationGenerated_conjugation,
    monsterSourcePermutationImage_code k d e ε he]
  rfl

/-- Every positive source cocode obeys its exact standard monomial action in G. -/
theorem monsterSourcePermutationGenerated_cocode (k : Fin 2) (δ : SpinIndex) :
    monsterSourcePermutationGenerated k * sourceGeneratedCocode δ *
      (monsterSourcePermutationGenerated k)⁻¹ =
      sourceGeneratedCocode (monsterMonomialPullback (monsterSourcePermutationCode k).symm δ) := by
  rw [sourceGeneratedCocode, monsterSourcePermutationGenerated_conjugation,
    monsterSourcePermutationImage_cocode]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
