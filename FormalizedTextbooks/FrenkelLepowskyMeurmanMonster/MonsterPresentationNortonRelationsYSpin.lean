/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source y-code spin candidates for all low eleven-bit code labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationYPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
variable (a : Fin 2048)

/-- The actual low source code label. -/
def monsterNortonYCode : SpinIndex := golayLabelCoefficients ⟨a.val, by omega⟩

/-- This label has no all-one-code component. -/
theorem monsterNortonYCode_last : (monsterNortonYCode a) 11 = 0 := by
  exact golayLabel_low_last a

/-- The linear part of the source affine relabeling in plus/minus coordinates. -/
def monsterNortonYShear : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun t := t + t 11 • (monsterNortonYCode a)
  invFun t := t + t 11 • (monsterNortonYCode a)
  left_inv t := by
    ext i
    change (t i + t 11 * (monsterNortonYCode a) i) +
      (t 11 + t 11 * (monsterNortonYCode a) 11) * (monsterNortonYCode a) i = t i
    rw [(monsterNortonYCode_last a), mul_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  right_inv t := by
    ext i
    change (t i + t 11 * (monsterNortonYCode a) i) +
      (t 11 + t 11 * (monsterNortonYCode a) 11) * (monsterNortonYCode a) i = t i
    rw [(monsterNortonYCode_last a), mul_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  map_add' t s := by ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  map_smul' c t := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The binary shear and its inverse have the same literal coordinate formula. -/
theorem monsterNortonYShear_symm : (monsterNortonYShear a).symm = (monsterNortonYShear a) := by
  apply LinearEquiv.ext
  intro t
  rfl

/-- The additive translation factor in the source affine relabeling is an actual Q element. -/
def monsterNortonYTranslation : Q :=
  ⟨ofAdd (Fin.append (monsterNortonYCode a) (0 : SpinIndex)), 1⟩

/-- This actual Q factor has precisely the advertised additive translation. -/
theorem monsterNortonYTranslation_translation :
    spinTranslation (monsterNortonYTranslation a) = (monsterNortonYCode a) := by
  ext i
  exact Fin.append_left _ _ i

/-- Its modulation is zero, so no extra sign is silently introduced. -/
theorem monsterNortonYTranslation_modulation :
    spinModulation (monsterNortonYTranslation a) = 0 := by
  ext i
  exact Fin.append_right _ _ i

/-- The additive translation has actual central phase zero on every spin label. -/
theorem monsterNortonYTranslation_phase (t : SpinIndex) :
    spinPhase (monsterNortonYTranslation a) t = 0 := by
  rw [spinPhase, (monsterNortonYTranslation_modulation a)]
  change (0 : ZMod 2) + spinDot 0 t = 0
  simp [spinDot]

/-- The complete plus/minus operator retains all actual quadratic phases. -/
noncomputable def monsterNortonYPlusMinus : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph (monsterSourceYPhaseMatrix (monsterNortonYCode a)) *
    monsterMonomialPermutationHolomorph (monsterNortonYShear a) *
      spinHolomorphIncl (monsterNortonYTranslation a)

/-- The actual operator has exactly the primary plus/minus signed affine formula. -/
theorem monsterNortonYPlusMinus_apply (f : SpinSpace) (t : SpinIndex) :
    (monsterNortonYPlusMinus a).val f t =
      qSign (spinDot (sourceCodeThetaPolynomial t) (monsterNortonYCode a) +
        t 11 * spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) t) *
          f (t + (1 + t 11) • (monsterNortonYCode a)) := by
  change qSign (monsterMonomialQuadratic (monsterSourceYPhaseMatrix (monsterNortonYCode a)) t) *
    spinRepresentation (monsterNortonYTranslation a) f ((monsterNortonYShear a).symm t) = _
  rw [monsterSourceYPhaseMatrix_apply, monsterMonomialSpinRepresentation_apply,
    (monsterNortonYTranslation_phase a), qSign_zero, one_mul,
    (monsterNortonYTranslation_translation a), (monsterNortonYShear_symm a)]
  apply congrArg (fun s : SpinIndex => qSign
    (spinDot (sourceCodeThetaPolynomial t) (monsterNortonYCode a) +
      t 11 * spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) t) * f s)
  ext i
  change (t i + t 11 * (monsterNortonYCode a) i) + (monsterNortonYCode a) i =
    t i + (1 + t 11) * (monsterNortonYCode a) i
  ring

/-- The explicit source y-code spin candidate in Schrödinger coordinates. -/
noncomputable def monsterNortonYSpin : SpinHolomorph :=
  monsterSpinHadamardHolomorph * (monsterNortonYPlusMinus a) * monsterSpinHadamardHolomorph

/-- Its actual extraspecial image, including every central correction from the Fourier factors. -/
def monsterNortonYImage (q : Q) : Q :=
  monsterSpinHadamardImage
    (monsterMonomialDiagonalImage (monsterSourceYPhaseMatrix (monsterNortonYCode a))
      (monsterMonomialPermutationImage (monsterNortonYShear a)
        ((monsterNortonYTranslation a) * monsterSpinHadamardImage q *
          (monsterNortonYTranslation a)⁻¹)))

/-- The explicit plus/minus product has the stated actual Q conjugation law. -/
theorem monsterNortonYPlusMinus_conjugation (q : Q) :
    spinConjugation (monsterNortonYPlusMinus a) q =
      monsterMonomialDiagonalImage (monsterSourceYPhaseMatrix (monsterNortonYCode a))
        (monsterMonomialPermutationImage (monsterNortonYShear a)
          ((monsterNortonYTranslation a) * q * (monsterNortonYTranslation a)⁻¹)) := by
  rw [monsterNortonYPlusMinus, map_mul, map_mul]
  change spinConjugation
    (monsterMonomialDiagonalHolomorph (monsterSourceYPhaseMatrix (monsterNortonYCode a)))
      (spinConjugation (monsterMonomialPermutationHolomorph (monsterNortonYShear a))
        (spinConjugation (spinHolomorphIncl (monsterNortonYTranslation a)) q)) = _
  rw [spinConjugation_incl, monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation]

/-- The full explicit source candidate has this actual all-Q conjugation automorphism. -/
theorem monsterNortonYSpin_conjugation (q : Q) :
    spinConjugation (monsterNortonYSpin a) q = (monsterNortonYImage a) q := by
  rw [monsterNortonYSpin, map_mul, map_mul]
  change spinConjugation monsterSpinHadamardHolomorph
    (spinConjugation (monsterNortonYPlusMinus a)
      (spinConjugation monsterSpinHadamardHolomorph q)) = _
  rw [monsterSpinHadamardHolomorph_conjugation, (monsterNortonYPlusMinus_conjugation a),
    monsterSpinHadamardHolomorph_conjugation]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
