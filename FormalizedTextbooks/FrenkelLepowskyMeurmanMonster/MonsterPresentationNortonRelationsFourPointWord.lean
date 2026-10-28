/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A concrete source-word transport of the common four-point Q class.
All Q conjugations retain the inverse source-permutation and central Parker phases. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYOpposite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLineCentralizer

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The short genuine source word whose binary projection transports the four-point class. -/
noncomputable def monsterNortonFourPointWord : ↥G :=
  xiSpinGenerated⁻¹ * (monsterSourcePermutationGenerated 1)⁻¹ * xiSpinGenerated *
    sourceGeneratedY 144 0 * xiSpinGenerated⁻¹

/-- Its explicit central-corrected action on every Q element. -/
noncomputable def monsterNortonFourPointWordImage (q : Q) : Q :=
  monsterNortonXiQImage (monsterNortonXiQImage
    (monsterNortonPermutationInverseImage 1
      (monsterNortonXiQImage
        (sourceQCode 144 0 * monsterNortonYImage 144
          (monsterNortonXiQImage (monsterNortonXiQImage q)) * (sourceQCode 144 0)⁻¹))))

private theorem conjugate_mul {Γ : Type*} [Group Γ] (a b g : Γ) :
    (a * b) * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ := by group

private theorem xi_inverse_conjugation (q : Q) :
    xiSpinGenerated⁻¹ * qIntoGenerated q * (xiSpinGenerated⁻¹)⁻¹ =
      qIntoGenerated (monsterNortonXiQImage (monsterNortonXiQImage q)) := by
  have hi : xiSpinGenerated⁻¹ = xiSpinGenerated * xiSpinGenerated := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [pow_succ, pow_zero, one_mul] using xiSpinGenerated_cube
  rw [hi, conjugate_mul, xiSpinGenerated_conjugation, xiSpinGenerated_conjugation]
  rfl

private theorem permutation_inverse_conjugation (q : Q) :
    (monsterSourcePermutationGenerated 1)⁻¹ * qIntoGenerated q *
      ((monsterSourcePermutationGenerated 1)⁻¹)⁻¹ =
        qIntoGenerated (monsterNortonPermutationInverseImage 1 q) := by
  have h := monsterFiberGenerated_conjugate_Q ((monsterSourcePermutationFiber 1)⁻¹) q
  change (monsterSourcePermutationGenerated 1)⁻¹ * qIntoGenerated q *
    ((monsterSourcePermutationGenerated 1)⁻¹)⁻¹ =
      qIntoGenerated (spinConjugation (monsterSourcePermutationSpin 1)⁻¹ q) at h
  rw [monsterNortonPermutationInverseImage_eq] at h
  exact h

private theorem y144_conjugation (q : Q) :
    sourceGeneratedY 144 0 * qIntoGenerated q * (sourceGeneratedY 144 0)⁻¹ =
      qIntoGenerated (sourceQCode 144 0 * monsterNortonYImage 144 q *
        (sourceQCode 144 0)⁻¹) := by
  have h := monsterNortonYOpposite_conjugation 144 (by decide +kernel) q
  have he : (⟨(144 : Fin 2048).val, by omega⟩ : Fin 4096) = 144 := by decide +kernel
  rw [he] at h
  exact h

/-- The displayed Q image is the actual conjugation by the concrete generated-group word. -/
theorem monsterNortonFourPointWord_conjugation (q : Q) :
    monsterNortonFourPointWord * qIntoGenerated q * monsterNortonFourPointWord⁻¹ =
      qIntoGenerated (monsterNortonFourPointWordImage q) := by
  rw [monsterNortonFourPointWord]
  simp only [conjugate_mul, xi_inverse_conjugation,
    y144_conjugation,
    xiSpinGenerated_conjugation, permutation_inverse_conjugation]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Kernel reduction checks all 24 bits through the full five-factor Q conjugation.
/-- The concrete Q word transports the actual four-point binary vector to the Omega vector. -/
theorem monsterNortonFourPointWord_binary : ∀ i : Fin 24,
    toAdd (monsterNortonFourPointWordImage
      (sourceQCocode (golayLabelCoefficients 924))).base i =
        toAdd sourceOmegaQ.base i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- The single central coefficient is evaluated through all source factors, including p1 inverse.
/-- The concrete transport has central phase one; this phase is retained in the final word. -/
theorem monsterNortonFourPointWord_phase :
    toAdd (monsterNortonFourPointWordImage
      (sourceQCocode (golayLabelCoefficients 924))).coeff = 1 := by
  decide +kernel

/-- The full actual Q image is the negative Omega lift, not merely its binary class. -/
theorem monsterNortonFourPointWord_image :
    monsterNortonFourPointWordImage (sourceQCocode (golayLabelCoefficients 924)) =
      qCentral 1 * sourceOmegaQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    funext i
    exact monsterNortonFourPointWord_binary i
  · apply toAdd.injective
    rw [qCentral_mul_coeff, monsterNortonFourPointWord_phase]
    change (1 : ZMod 2) = 1 + 0
    rw [add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
