/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The explicit source y82 spin candidate from Seysen Table 3.
Its source plus/minus coordinates use the signed affine relabeling with phase
theta(t) dot e + t11*(theta(e) dot t). The actual Schrödinger coordinates are
obtained by the verified one-coordinate Fourier operator on both sides.
The result is an actual orthogonal normalizer; equality with triality-conjugated
x82 on the full Griess space is a separate obligation, not an assumption here.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationYPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual source code label 0x52. -/
def monsterSourceY82Code : SpinIndex := golayLabelCoefficients 82

/-- This label has no all-one-code component. -/
theorem monsterSourceY82Code_last : monsterSourceY82Code 11 = 0 := by decide +kernel

/-- The linear part of the source affine relabeling in plus/minus coordinates. -/
def monsterSourceY82Shear : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun t := t + t 11 • monsterSourceY82Code
  invFun t := t + t 11 • monsterSourceY82Code
  left_inv t := by
    ext i
    change (t i + t 11 * monsterSourceY82Code i) +
      (t 11 + t 11 * monsterSourceY82Code 11) * monsterSourceY82Code i = t i
    rw [monsterSourceY82Code_last, mul_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  right_inv t := by
    ext i
    change (t i + t 11 * monsterSourceY82Code i) +
      (t 11 + t 11 * monsterSourceY82Code 11) * monsterSourceY82Code i = t i
    rw [monsterSourceY82Code_last, mul_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  map_add' t s := by ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  map_smul' c t := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The binary shear and its inverse have the same literal coordinate formula. -/
theorem monsterSourceY82Shear_symm : monsterSourceY82Shear.symm = monsterSourceY82Shear := by
  apply LinearEquiv.ext
  intro t
  rfl

/-- The additive translation factor in the source affine relabeling is an actual Q element. -/
def monsterSourceY82Translation : Q :=
  ⟨ofAdd (Fin.append monsterSourceY82Code (0 : SpinIndex)), 1⟩

/-- This actual Q factor has precisely the advertised additive translation. -/
theorem monsterSourceY82Translation_translation :
    spinTranslation monsterSourceY82Translation = monsterSourceY82Code := by
  ext i
  exact Fin.append_left _ _ i

/-- Its modulation is zero, so no extra sign is silently introduced. -/
theorem monsterSourceY82Translation_modulation :
    spinModulation monsterSourceY82Translation = 0 := by
  ext i
  exact Fin.append_right _ _ i

/-- The additive translation has actual central phase zero on every spin label. -/
theorem monsterSourceY82Translation_phase (t : SpinIndex) :
    spinPhase monsterSourceY82Translation t = 0 := by
  rw [spinPhase, monsterSourceY82Translation_modulation]
  change (0 : ZMod 2) + spinDot 0 t = 0
  simp [spinDot]

/-- The complete plus/minus operator retains all actual quadratic phases. -/
noncomputable def monsterSourceY82PlusMinus : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph (monsterSourceYPhaseMatrix monsterSourceY82Code) *
    monsterMonomialPermutationHolomorph monsterSourceY82Shear *
      spinHolomorphIncl monsterSourceY82Translation

/-- The actual operator has exactly the primary plus/minus signed affine formula. -/
theorem monsterSourceY82PlusMinus_apply (f : SpinSpace) (t : SpinIndex) :
    monsterSourceY82PlusMinus.val f t =
      qSign (spinDot (sourceCodeThetaPolynomial t) monsterSourceY82Code +
        t 11 * spinDot (sourceCodeThetaPolynomial monsterSourceY82Code) t) *
          f (t + (1 + t 11) • monsterSourceY82Code) := by
  change qSign (monsterMonomialQuadratic (monsterSourceYPhaseMatrix monsterSourceY82Code) t) *
    spinRepresentation monsterSourceY82Translation f (monsterSourceY82Shear.symm t) = _
  rw [monsterSourceYPhaseMatrix_apply, monsterMonomialSpinRepresentation_apply,
    monsterSourceY82Translation_phase, qSign_zero, one_mul,
    monsterSourceY82Translation_translation, monsterSourceY82Shear_symm]
  apply congrArg (fun s : SpinIndex => qSign
    (spinDot (sourceCodeThetaPolynomial t) monsterSourceY82Code +
      t 11 * spinDot (sourceCodeThetaPolynomial monsterSourceY82Code) t) * f s)
  ext i
  change (t i + t 11 * monsterSourceY82Code i) + monsterSourceY82Code i =
    t i + (1 + t 11) * monsterSourceY82Code i
  ring

/-- The explicit source y82 spin candidate in Schrödinger coordinates. -/
noncomputable def monsterSourceY82Spin : SpinHolomorph :=
  monsterSpinHadamardHolomorph * monsterSourceY82PlusMinus * monsterSpinHadamardHolomorph

/-- Its actual extraspecial image, including every central correction from the Fourier factors. -/
def monsterSourceY82Image (q : Q) : Q :=
  monsterSpinHadamardImage
    (monsterMonomialDiagonalImage (monsterSourceYPhaseMatrix monsterSourceY82Code)
      (monsterMonomialPermutationImage monsterSourceY82Shear
        (monsterSourceY82Translation * monsterSpinHadamardImage q *
          monsterSourceY82Translation⁻¹)))

/-- The explicit plus/minus product has the stated actual Q conjugation law. -/
theorem monsterSourceY82PlusMinus_conjugation (q : Q) :
    spinConjugation monsterSourceY82PlusMinus q =
      monsterMonomialDiagonalImage (monsterSourceYPhaseMatrix monsterSourceY82Code)
        (monsterMonomialPermutationImage monsterSourceY82Shear
          (monsterSourceY82Translation * q * monsterSourceY82Translation⁻¹)) := by
  rw [monsterSourceY82PlusMinus, map_mul, map_mul]
  change spinConjugation
    (monsterMonomialDiagonalHolomorph (monsterSourceYPhaseMatrix monsterSourceY82Code))
      (spinConjugation (monsterMonomialPermutationHolomorph monsterSourceY82Shear)
        (spinConjugation (spinHolomorphIncl monsterSourceY82Translation) q)) = _
  rw [spinConjugation_incl, monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation]

/-- The full explicit source candidate has this actual all-Q conjugation automorphism. -/
theorem monsterSourceY82Spin_conjugation (q : Q) :
    spinConjugation monsterSourceY82Spin q = monsterSourceY82Image q := by
  rw [monsterSourceY82Spin, map_mul, map_mul]
  change spinConjugation monsterSpinHadamardHolomorph
    (spinConjugation monsterSourceY82PlusMinus
      (spinConjugation monsterSpinHadamardHolomorph q)) = _
  rw [monsterSpinHadamardHolomorph_conjugation, monsterSourceY82PlusMinus_conjugation,
    monsterSpinHadamardHolomorph_conjugation]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
