/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Symbolic pair-lift conjugation needed to compare the actual y82 candidate's matrix rows. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCodeDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A coordinate Q lift with its actual central coefficient retained explicitly. -/
def monsterY82CoordinateLift (a b : SpinIndex) (c : ZMod 2) : Q :=
  ⟨ofAdd (Fin.append a b), ofAdd c⟩

/-- Translation of the actual coordinate lift. -/
theorem monsterY82CoordinateLift_translation (a b : SpinIndex) (c : ZMod 2) :
    spinTranslation (monsterY82CoordinateLift a b c) = a := by
  ext i
  exact Fin.append_left _ _ i

/-- Modulation of the same actual coordinate lift. -/
theorem monsterY82CoordinateLift_modulation (a b : SpinIndex) (c : ZMod 2) :
    spinModulation (monsterY82CoordinateLift a b c) = b := by
  ext i
  exact Fin.append_right _ _ i

/-- The central coefficient is exactly the displayed coefficient. -/
theorem monsterY82CoordinateLift_coeff (a b : SpinIndex) (c : ZMod 2) :
    toAdd (monsterY82CoordinateLift a b c).coeff = c := rfl

/-- Coordinate equalities determine the actual Q element, including its central sign. -/
theorem monsterY82CoordinateLift_eq (q : Q) (a b : SpinIndex) (c : ZMod 2)
    (ha : spinTranslation q = a) (hb : spinModulation q = b) (hc : toAdd q.coeff = c) :
    q = monsterY82CoordinateLift a b c := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply (qBase_eq_iff_spin_coordinates _ _).mpr
    exact ⟨ha.trans (monsterY82CoordinateLift_translation a b c).symm,
      hb.trans (monsterY82CoordinateLift_modulation a b c).symm⟩
  · apply Multiplicative.toAdd.injective
    exact hc

/-- Pullback by the source shear adds its precise code character on the last coordinate. -/
theorem monsterSourceY82Shear_pullback (b : SpinIndex) :
    monsterMonomialPullback monsterSourceY82Shear b =
      b + spinDot b monsterSourceY82Code • monsterSpinOmegaVector := by
  ext i
  change spinDot b ((Pi.single i 1 : SpinIndex) +
      (Pi.single i 1 : SpinIndex) 11 • monsterSourceY82Code) =
    b i + spinDot b monsterSourceY82Code * monsterSpinOmegaVector i
  rw [spinDot_add_right, xiSpinDot_smul_right]
  have hi : spinDot b (Pi.single i 1) = b i := by simp [spinDot, Pi.single_apply]
  rw [hi]
  by_cases h : i = 11
  · subst i
    simp [monsterSpinOmegaVector]
  · simp [monsterSpinOmegaVector, h, eq_comm]

/-- Fourier swaps a last-coordinate translation into the same actual even cocode. -/
theorem monsterY82CoordinateLift_hadamard (s c : ZMod 2) (δ : SpinIndex) (hδ : δ 11 = 0) :
    monsterSpinHadamardImage (monsterY82CoordinateLift (s • monsterSpinOmegaVector) δ c) =
      monsterY82CoordinateLift 0 (δ + s • monsterSpinOmegaVector) c := by
  apply monsterY82CoordinateLift_eq
  · rw [monsterSpinHadamardImage_translation, monsterY82CoordinateLift_translation,
      monsterY82CoordinateLift_modulation, hδ, add_zero]
    ext i
    change s * monsterSpinOmegaVector i +
      (s * monsterSpinOmegaVector 11) * monsterSpinOmegaVector i = 0
    change s * monsterSpinOmegaVector i + (s * 1) * monsterSpinOmegaVector i = 0
    rw [mul_one, CharTwo.add_self_eq_zero]
  · rw [monsterSpinHadamardImage_modulation, monsterY82CoordinateLift_translation,
      monsterY82CoordinateLift_modulation, hδ, add_zero]
    change δ + (s * 1) • monsterSpinOmegaVector = δ + s • monsterSpinOmegaVector
    rw [mul_one]
  · change c + (s • monsterSpinOmegaVector) 11 * δ 11 = c
    rw [hδ, mul_zero, add_zero]

/-- Fourier sends the same even cocode back to its last-coordinate translation. -/
theorem monsterY82CoordinateLift_hadamard_reverse (s c : ZMod 2)
    (δ : SpinIndex) (hδ : δ 11 = 0) :
    monsterSpinHadamardImage (monsterY82CoordinateLift 0 (δ + s • monsterSpinOmegaVector) c) =
      monsterY82CoordinateLift (s • monsterSpinOmegaVector) δ c := by
  apply monsterY82CoordinateLift_eq
  · rw [monsterSpinHadamardImage_translation, monsterY82CoordinateLift_translation,
      monsterY82CoordinateLift_modulation]
    simp [Pi.add_apply, Pi.smul_apply, monsterSpinOmegaVector, hδ]
  · rw [monsterSpinHadamardImage_modulation, monsterY82CoordinateLift_translation,
      monsterY82CoordinateLift_modulation]
    ext i
    change (δ i + s * monsterSpinOmegaVector i) +
      (0 + (δ 11 + s * monsterSpinOmegaVector 11)) * monsterSpinOmegaVector i = δ i
    change (δ i + s * monsterSpinOmegaVector i) +
      (0 + (δ 11 + s * 1)) * monsterSpinOmegaVector i = δ i
    rw [hδ, mul_one, zero_add, zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · change c + (0 : SpinIndex) 11 * (δ + s • monsterSpinOmegaVector) 11 = c
    simp

/-- Multiplication by an actual central element changes only the displayed central coefficient. -/
theorem monsterY82CoordinateLift_central_mul (a b : SpinIndex) (c z : ZMod 2) :
    qCentral z * monsterY82CoordinateLift a b c = monsterY82CoordinateLift a b (z + c) := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    rfl
  · apply Multiplicative.toAdd.injective
    rw [qCentral_mul_coeff, monsterY82CoordinateLift_coeff, monsterY82CoordinateLift_coeff]

/-- The actual affine translation contributes exactly its cocode character to conjugation. -/
theorem monsterY82CoordinateLift_translation_conjugate (b : SpinIndex) (c : ZMod 2) :
    monsterSourceY82Translation * monsterY82CoordinateLift 0 b c *
      monsterSourceY82Translation⁻¹ =
        monsterY82CoordinateLift 0 b (c + spinDot monsterSourceY82Code b) := by
  rw [q_conjugation_central_phase, qBeta_spin_coordinates, qBeta_spin_coordinates,
    monsterSourceY82Translation_translation, monsterSourceY82Translation_modulation,
    monsterY82CoordinateLift_translation, monsterY82CoordinateLift_modulation]
  simp only [spinDot_zero_left, add_zero]
  rw [monsterY82CoordinateLift_central_mul, add_comm]

/-- The actual relabeling image has the displayed pullback modulation. -/
theorem monsterY82PermutationImage_modulation
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) :
    spinModulation (monsterMonomialPermutationImage P q) =
      monsterMonomialPullback P.symm (spinModulation q) := by
  ext i
  exact Fin.append_right _ _ i

/-- The actual quadratic image has its displayed derivative modulation. -/
theorem monsterY82DiagonalImage_modulation (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) :
    spinModulation (monsterMonomialDiagonalImage M q) =
      spinModulation q + monsterMonomialGradient M (spinTranslation q) := by
  ext i
  exact Fin.append_right _ _ i

/-- The actual quadratic image retains its full central coefficient correction. -/
theorem monsterY82DiagonalImage_coeff (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) :
    toAdd (monsterMonomialDiagonalImage M q).coeff = toAdd q.coeff +
      monsterMonomialQuadratic M (spinTranslation q) := rfl

/-- The actual shear relabeling pulls the even cocode back by the precise source character. -/
theorem monsterY82CoordinateLift_permutation (b : SpinIndex) (c : ZMod 2) :
    monsterMonomialPermutationImage monsterSourceY82Shear (monsterY82CoordinateLift 0 b c) =
      monsterY82CoordinateLift 0
        (b + spinDot b monsterSourceY82Code • monsterSpinOmegaVector) c := by
  apply monsterY82CoordinateLift_eq
  · rw [monsterMonomialPermutationImage_translation, monsterY82CoordinateLift_translation,
      map_zero]
  · rw [monsterY82PermutationImage_modulation, monsterY82CoordinateLift_modulation]
    rw [monsterSourceY82Shear_symm, monsterSourceY82Shear_pullback]
  · rfl

/-- A pure cocode has no quadratic translation derivative or phase correction. -/
theorem monsterY82CoordinateLift_diagonal (b : SpinIndex) (c : ZMod 2) :
    monsterMonomialDiagonalImage (monsterSourceYPhaseMatrix monsterSourceY82Code)
      (monsterY82CoordinateLift 0 b c) = monsterY82CoordinateLift 0 b c := by
  apply monsterY82CoordinateLift_eq
  · rw [monsterMonomialDiagonalImage_translation, monsterY82CoordinateLift_translation]
  · rw [monsterY82DiagonalImage_modulation, monsterY82CoordinateLift_modulation,
      monsterY82CoordinateLift_translation]
    ext i
    simp [monsterMonomialGradient]
  · rw [monsterY82DiagonalImage_coeff, monsterY82CoordinateLift_coeff,
      monsterY82CoordinateLift_translation]
    simp [monsterMonomialQuadratic]

/-- The actual source spin candidate has this symbolic conjugation law on every even pair lift. -/
theorem monsterSourceY82Image_even (s c : ZMod 2) (δ : SpinIndex) (hδ : δ 11 = 0) :
    monsterSourceY82Image (monsterY82CoordinateLift (s • monsterSpinOmegaVector) δ c) =
      monsterY82CoordinateLift
        ((s + spinDot δ monsterSourceY82Code) • monsterSpinOmegaVector) δ
          (c + spinDot δ monsterSourceY82Code) := by
  rw [monsterSourceY82Image, monsterY82CoordinateLift_hadamard s c δ hδ,
    monsterY82CoordinateLift_translation_conjugate, monsterY82CoordinateLift_permutation,
    monsterY82CoordinateLift_diagonal]
  have hb : (δ + s • monsterSpinOmegaVector) +
      spinDot (δ + s • monsterSpinOmegaVector) monsterSourceY82Code • monsterSpinOmegaVector =
        δ + (s + spinDot δ monsterSourceY82Code) • monsterSpinOmegaVector := by
    rw [spinDot_add_left, xiSpinDot_smul_left, monsterSpinOmegaVector_dot,
      monsterSourceY82Code_last, mul_zero, add_zero]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hc : c + spinDot monsterSourceY82Code (δ + s • monsterSpinOmegaVector) =
      c + spinDot δ monsterSourceY82Code := by
    rw [spinDot_add_right, xiSpinDot_smul_right, monsterSpinOmegaVector_dot_right,
      monsterSourceY82Code_last, mul_zero, add_zero, spinDot_comm monsterSourceY82Code δ]
  rw [hb, hc]
  exact monsterY82CoordinateLift_hadamard_reverse _ _ δ hδ

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
