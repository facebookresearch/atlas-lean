/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full p1460160 square relation in the actual spin, local and generated groups. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialP1Square

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The compact matrix computes exactly the defining source quadratic cochain. -/
theorem monsterSourcePermutationPhaseData_apply (k : Fin 2) (a : SpinIndex) :
    monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) a =
      monsterSourcePermutationPhase k a := by
  rw [monsterSourcePermutationPhaseData_eq]
  rfl

/-- The actual source spin lift evaluates by its explicit signed relabeling. -/
theorem monsterSourcePermutationSpin_apply (k : Fin 2) (f : SpinSpace) (t : SpinIndex) :
    (monsterSourcePermutationSpin k).val f t =
      qSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData k)
        ((monsterSourcePermutationCode k).symm t)) *
          f ((monsterSourcePermutationCode k).symm t) := rfl

/-- Positive source cocodes act by their actual Schrödinger characters. -/
theorem monsterSourceQCocode_spin (δ : SpinIndex) (f : SpinSpace) (t : SpinIndex) :
    spinRepresentation (sourceQCocode δ) f t = qSign (spinDot δ t) * f t := by
  have hc : toAdd (sourceQCocode δ).coeff = 0 := rfl
  have hp : spinPhase (sourceQCocode δ) t = spinDot δ t := by
    rw [spinPhase, sourceQCocode_modulation, hc, zero_add]
  rw [monsterMonomialSpinRepresentation_apply, hp, sourceQCocode_translation, add_zero]

/-- The source square character is the exact square of the actual spin lift. -/
theorem monsterSourcePermutationP1_spin_square :
    monsterSourcePermutationSpin 1 ^ 2 =
      spinHolomorphIncl (sourceQCocode monsterSourcePermutationP1SquareCocode) := by
  rw [pow_two]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro f
  ext t
  change (monsterSourcePermutationSpin 1).val
    ((monsterSourcePermutationSpin 1).val f) t =
      spinRepresentation (sourceQCocode monsterSourcePermutationP1SquareCocode) f t
  simp only [monsterSourcePermutationSpin_apply, monsterSourcePermutationP1_code_symm,
    monsterSourcePermutationP1_code_square, monsterSourcePermutationPhaseData_apply,
    monsterSourceQCocode_spin]
  rw [← mul_assoc, ← qSign_add,
    add_comm (monsterSourcePermutationPhase 1 (monsterSourcePermutationCode 1 t))
      (monsterSourcePermutationPhase 1 t), monsterSourcePermutationP1SquarePhase_character]

/-- The same source coordinate permutation has square one on the actual Leech lattice. -/
theorem monsterSourcePermutationP1_leech_square : omegaOrbitPermutationIsometry 1 ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro f
  ext i
  change f ((omegaOrbitPermutation 1).symm ((omegaOrbitPermutation 1).symm i)) = f i
  have hi : ∀ j : Fin 24,
      (omegaOrbitPermutation 1).symm ((omegaOrbitPermutation 1).symm j) = j := by
    decide +kernel
  rw [hi]

/-- The exact fiber element squares to the positive source cocode, before any quotient. -/
theorem monsterSourcePermutationP1_fiber_square :
    monsterSourcePermutationFiber 1 ^ 2 =
      localFiberIncl (sourceQCocode monsterSourcePermutationP1SquareCocode) := by
  apply Subtype.ext
  apply Prod.ext
  · exact monsterSourcePermutationP1_spin_square
  · exact monsterSourcePermutationP1_leech_square

/-- The source Parker square relation holds in the actual simultaneous-sign quotient H. -/
theorem monsterSourcePermutationP1_local_square :
    monsterSourcePermutationLocal 1 ^ 2 =
      inclQ (sourceQCocode monsterSourcePermutationP1SquareCocode) := by
  change (QuotientGroup.mk' localDiagonalSubgroup (monsterSourcePermutationFiber 1)) ^ 2 =
    QuotientGroup.mk' localDiagonalSubgroup
      (localFiberIncl (sourceQCocode monsterSourcePermutationP1SquareCocode))
  rw [← map_pow, monsterSourcePermutationP1_fiber_square]

/-- The genuine named-group source lift squares to the exact cocode 0x203. -/
theorem monsterSourcePermutationP1_generated_square :
    monsterSourcePermutationGenerated 1 ^ 2 =
      sourceGeneratedCocode (golayLabelCoefficients 515) := by
  rw [monsterSourcePermutationGenerated, ← map_pow, monsterSourcePermutationP1_local_square]
  rfl

/-- The inverse source assignment includes the exact cocode correction of the Parker lift. -/
theorem monsterSourcePermutationP1_generated_inverse :
    (monsterSourcePermutationGenerated 1)⁻¹ =
      sourceGeneratedCocode (golayLabelCoefficients 515) *
        monsterSourcePermutationGenerated 1 := by
  have hc : (sourceGeneratedCocode (golayLabelCoefficients 515))⁻¹ =
      sourceGeneratedCocode (golayLabelCoefficients 515) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, sourceGeneratedCocode_square]
  calc
    (monsterSourcePermutationGenerated 1)⁻¹ =
        (monsterSourcePermutationGenerated 1 ^ 2)⁻¹ *
          monsterSourcePermutationGenerated 1 := by
      rw [pow_two, mul_inv_rev, inv_mul_cancel_right]
    _ = _ := by rw [monsterSourcePermutationP1_generated_square, hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
