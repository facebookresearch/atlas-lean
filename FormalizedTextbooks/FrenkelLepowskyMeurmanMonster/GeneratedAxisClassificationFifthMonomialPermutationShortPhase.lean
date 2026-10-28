/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPreferredQ

/-! The original signed monomial polynomial determines the true central conjugation phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem sign_injective : Function.Injective qSign := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | norm_num [qSign] at h

/-- Evaluate the genuine intertwining identity on the constant spin vector at zero. -/
theorem generatedFifth_monomial_conjugation_coefficient (g : SpinHolomorph)
    (P M : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hg : representativeSpinCertificate g P M) (q : Q) :
    toAdd (spinConjugation g q).coeff = toAdd q.coeff +
      monsterMonomialQuadratic M (spinTranslation (spinConjugation g q)) := by
  have hi : spinRepresentation (spinConjugation g q) * g.val =
      g.val * spinRepresentation q := by
    rw [spinConjugation_representation]
    group
  have hh := congrArg (fun e : SpinSpace ≃ₗ[ℝ] SpinSpace => e (fun _ => 1) 0) hi
  simp only [LinearEquiv.mul_apply] at hh
  rw [monsterMonomialSpinRepresentation_apply, hg, hg,
    monsterMonomialSpinRepresentation_apply] at hh
  simp only [Matrix.mulVec_zero, spinPhase, spinDot_zero_right,
    add_zero, zero_add, mul_one] at hh
  have hz : monsterMonomialQuadratic M 0 = 0 := by
    simp [monsterMonomialQuadratic]
  rw [hz, qSign_zero, one_mul] at hh
  apply sign_injective
  rw [qSign_add]
  symm
  calc
    _ = (qSign (toAdd (spinConjugation g q).coeff) *
        qSign (monsterMonomialQuadratic M (spinTranslation (spinConjugation g q)))) *
          qSign (monsterMonomialQuadratic M (spinTranslation (spinConjugation g q))) := by
      rw [hh]
    _ = _ := by rw [mul_assoc, qSign_sq, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
