/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Concrete code and cocode generators in the extraspecial group and in G.
Source: Seysen, arXiv:2002.10921v3, §§5.2, 6.1 and 7.1.
The code lift has translation d, modulation θ(d), and central phase
ε+P(d), so multiplying by x_θ(d) gives the additive translation lift.
A source cocode has translation zero. The square and commutator calculations below
use the actual coordinate cocycle, rather than assumed presentation laws.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalSubgroups

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
-- The named coordinate group is an abbreviation of the cocycle extension.
set_option backward.isDefEq.respectTransparency false

/-- A signed source code lift x_d. Its central coordinate includes P(d),
as required by the additive normalization in Seysen (5.3.4)–(5.3.5). -/
def sourceQCode (d : Fin 4096) (ε : ZMod 2 := 0) : Q :=
  ⟨ofAdd (sourceExpectedCodeCoordinates (golayLabelCoefficients d)),
    ofAdd (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ))⟩

/-- The positive source cocode lift x_δ. -/
def sourceQCocode (δ : Fin 12 → ZMod 2) : Q :=
  ⟨ofAdd (binaryCocodeEmbedding δ), 1⟩

@[simp] theorem sourceQCode_translation (d : Fin 4096) (ε : ZMod 2) :
    spinTranslation (sourceQCode d ε) = golayLabelCoefficients d := by
  ext i
  simp [spinTranslation, sourceQCode, sourceExpectedCodeCoordinates]

@[simp] theorem sourceQCode_modulation (d : Fin 4096) (ε : ZMod 2) :
    spinModulation (sourceQCode d ε) = sourceCodeThetaPolynomial (golayLabelCoefficients d) := by
  ext i
  change Fin.append (golayLabelCoefficients d)
    (sourceCodeThetaPolynomial (golayLabelCoefficients d)) (Fin.natAdd 12 i) = _
  exact Fin.append_right _ _ _

@[simp] theorem sourceQCocode_translation (δ : Fin 12 → ZMod 2) :
    spinTranslation (sourceQCocode δ) = 0 := by
  ext i
  simp [spinTranslation, sourceQCocode, binaryCocodeEmbedding]

@[simp] theorem sourceQCocode_modulation (δ : Fin 12 → ZMod 2) :
    spinModulation (sourceQCocode δ) = δ := by
  ext i
  change binaryCocodeEmbedding δ (Fin.natAdd 12 i) = δ i
  exact binaryCocodeEmbedding_right _ _

private theorem qBeta_sourceExpectedCode (a : Fin 12 → ZMod 2) :
    qBeta (sourceExpectedCodeCoordinates a) (sourceExpectedCodeCoordinates a) =
      spinDot (sourceCodeThetaPolynomial a) a := by
  simp only [qBeta, sourceExpectedCodeCoordinates, Fin.append_left, Fin.append_right,
    spinDot, mul_comm]

/-- The source code square is the central sign prescribed by quarter-weight parity. -/
theorem sourceQCode_square (d : Fin 4096) (ε : ZMod 2) :
    sourceQCode d ε ^ 2 = qCentral (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  rw [pow_two]
  apply NormalizedCocycleExtension.Extension.ext
  · exact q_square_base _
  · apply toAdd.injective
    change (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) +
      (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) +
      qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients d))
      (sourceExpectedCodeCoordinates (golayLabelCoefficients d)) = _
    rw [CharTwo.add_self_eq_zero, zero_add, qBeta_sourceExpectedCode]
    exact sourceCodeThetaPolynomial_self_dot d

@[simp] theorem sourceQCocode_mul (δ η : Fin 12 → ZMod 2) :
    sourceQCocode δ * sourceQCocode η = sourceQCocode (δ + η) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change binaryCocodeEmbedding δ + binaryCocodeEmbedding η = binaryCocodeEmbedding (δ + η)
    exact (map_add binaryCocodeEmbedding δ η).symm
  · apply toAdd.injective
    change 0 + 0 + qBeta (binaryCocodeEmbedding δ) (binaryCocodeEmbedding η) = 0
    simp [qBeta, binaryCocodeEmbedding]

@[simp] theorem sourceQCocode_zero : sourceQCocode 0 = 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change binaryCocodeEmbedding 0 = 0
    exact map_zero _
  · rfl

@[simp] theorem sourceQCocode_square (δ : Fin 12 → ZMod 2) :
    sourceQCocode δ ^ 2 = 1 := by
  rw [pow_two, sourceQCocode_mul]
  have h : δ + δ = 0 := by ext i; exact CharTwo.add_self_eq_zero _
  rw [h, sourceQCocode_zero]

/-- Code and cocode generators commute up to their actual binary character. -/
theorem sourceQCode_cocode_swap (d : Fin 4096) (ε : ZMod 2) (δ : Fin 12 → ZMod 2) :
    sourceQCode d ε * sourceQCocode δ =
      qCentral (spinDot δ (golayLabelCoefficients d)) *
        (sourceQCocode δ * sourceQCode d ε) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change sourceExpectedCodeCoordinates (golayLabelCoefficients d) +
      binaryCocodeEmbedding δ = 0 +
        (binaryCocodeEmbedding δ + sourceExpectedCodeCoordinates (golayLabelCoefficients d))
    rw [zero_add, add_comm]
  · apply toAdd.injective
    change (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) + 0 +
      qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients d))
      (binaryCocodeEmbedding δ) =
      spinDot δ (golayLabelCoefficients d) +
        (0 + (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) +
          qBeta (binaryCocodeEmbedding δ)
          (sourceExpectedCodeCoordinates (golayLabelCoefficients d))) +
        qBeta 0 (binaryCocodeEmbedding δ +
          sourceExpectedCodeCoordinates (golayLabelCoefficients d))
    simp only [add_zero, zero_add, qBeta_zero_left]
    have hleft : qBeta (binaryCocodeEmbedding δ)
        (sourceExpectedCodeCoordinates (golayLabelCoefficients d)) = 0 := by
      simp [qBeta, binaryCocodeEmbedding]
    rw [hleft, add_zero]
    change (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) +
      (∑ i, golayLabelCoefficients d i * binaryCocodeEmbedding δ (Fin.natAdd 12 i)) = _
    simp only [binaryCocodeEmbedding_right, spinDot]
    simp only [mul_comm, add_comm]

/-- A pure additive translation, with an optional central sign. -/
def sourceQTranslation (a : Fin 12 → ZMod 2) (ε : ZMod 2 := 0) : Q :=
  ⟨ofAdd (Fin.append a (0 : Fin 12 → ZMod 2)), ofAdd ε⟩

/-- Source normalization (5.3.4): x_d x_θ(d) is the additive translation lift.
This fixes the central phase of every code word, including weight-twelve words. -/
theorem sourceQCode_theta_normalization (d : Fin 4096) (ε : ZMod 2) :
    sourceQCode d ε * sourceQCocode (sourceCodeThetaPolynomial (golayLabelCoefficients d)) =
      sourceQTranslation (golayLabelCoefficients d) ε := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change sourceExpectedCodeCoordinates (golayLabelCoefficients d) +
      binaryCocodeEmbedding (sourceCodeThetaPolynomial (golayLabelCoefficients d)) =
        Fin.append (golayLabelCoefficients d) (0 : Fin 12 → ZMod 2)
    ext i
    refine Fin.addCases (m := 12) (n := 12) ?_ ?_ i
    · intro j
      simp only [Pi.add_apply, sourceExpectedCodeCoordinates, Fin.append_left,
        binaryCocodeEmbedding_left, add_zero]
    · intro j
      simp only [Pi.add_apply, sourceExpectedCodeCoordinates, Fin.append_right,
        binaryCocodeEmbedding_right, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
  · apply toAdd.injective
    change (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) + 0 +
      qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients d))
        (binaryCocodeEmbedding (sourceCodeThetaPolynomial (golayLabelCoefficients d))) = ε
    have h : qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients d))
        (binaryCocodeEmbedding (sourceCodeThetaPolynomial (golayLabelCoefficients d))) =
        spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients d))
          (golayLabelCoefficients d) := by
      simp only [qBeta, sourceExpectedCodeCoordinates, Fin.append_left,
        binaryCocodeEmbedding_right, spinDot, mul_comm]
    rw [h, sourceCodeThetaPolynomial_self_dot, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]

/-- Pure translations have the source's additive multiplication law (5.3.5). -/
theorem sourceQTranslation_mul (a b : Fin 12 → ZMod 2) (ε η : ZMod 2) :
    sourceQTranslation a ε * sourceQTranslation b η = sourceQTranslation (a + b) (ε + η) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append a (0 : Fin 12 → ZMod 2) + Fin.append b (0 : Fin 12 → ZMod 2) =
      Fin.append (a + b) (0 : Fin 12 → ZMod 2)
    ext i
    refine Fin.addCases (m := 12) (n := 12) ?_ ?_ i
    · intro j
      simp only [Pi.add_apply, Fin.append_left]
    · intro j
      simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply, zero_add]
  · apply toAdd.injective
    change ε + η + qBeta (Fin.append a (0 : Fin 12 → ZMod 2))
      (Fin.append b (0 : Fin 12 → ZMod 2)) = ε + η
    simp only [qBeta, Fin.append_left, Fin.append_right, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero]

/-- Code source generators in the named generated group. -/
noncomputable def sourceGeneratedCode (d : Fin 4096) (ε : ZMod 2 := 0) : ↥G :=
  qIntoGenerated (sourceQCode d ε)

/-- Cocode source generators in the named generated group. -/
noncomputable def sourceGeneratedCocode (δ : Fin 12 → ZMod 2) : ↥G :=
  qIntoGenerated (sourceQCocode δ)

/-- The source y_d is x_d^τ, with the convention g^τ=τ⁻¹gτ.
Membership in the local subgroup is a separate coordinate calculation. -/
noncomputable def sourceGeneratedY (d : Fin 4096) (ε : ZMod 2 := 0) : ↥G :=
  extraIntoGenerated⁻¹ * sourceGeneratedCode d ε * extraIntoGenerated

theorem sourceGeneratedCode_square (d : Fin 4096) (ε : ZMod 2) :
    sourceGeneratedCode d ε ^ 2 =
      qIntoGenerated (qCentral (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) := by
  rw [sourceGeneratedCode, ← map_pow, sourceQCode_square]

@[simp] theorem sourceGeneratedCocode_square (δ : Fin 12 → ZMod 2) :
    sourceGeneratedCocode δ ^ 2 = 1 := by
  rw [sourceGeneratedCocode, ← map_pow, sourceQCocode_square, map_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
