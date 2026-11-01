/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit central-corrected extraspecial action of the complete actual Norton u word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPointLine

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual inverse source-permutation action, keeping the inverse Parker phase. -/
def monsterNortonPermutationInverseImage (k : Fin 2) (q : Q) : Q :=
  monsterMonomialDiagonalImage (monsterSourcePermutationPhaseData k)
    (monsterMonomialPermutationImage (monsterSourcePermutationCode k).symm q)

/-- The formula is the genuine inverse spin conjugation, not just its binary quotient. -/
theorem monsterNortonPermutationInverseImage_eq (k : Fin 2) (q : Q) :
    spinConjugation (monsterSourcePermutationSpin k)⁻¹ q =
      monsterNortonPermutationInverseImage k q := by
  have hd (M : Fin 12 → Fin 12 → ZMod 2) :
      (monsterMonomialDiagonalHolomorph M)⁻¹ = monsterMonomialDiagonalHolomorph M := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  have hp (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
      (monsterMonomialPermutationHolomorph P)⁻¹ = monsterMonomialPermutationHolomorph P.symm := by
    apply Subtype.ext
    exact (monsterMonomialPermutation_symm P).symm
  rw [monsterSourcePermutationSpin, mul_inv_rev, hd, hp, map_mul]
  change spinConjugation (monsterMonomialDiagonalHolomorph (monsterSourcePermutationPhaseData k))
    (spinConjugation
      (monsterMonomialPermutationHolomorph (monsterSourcePermutationCode k).symm) q) = _
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation]
  rfl

/-- The displayed complete ξ conjugation on actual Q. -/
noncomputable def monsterNortonXiQImage (q : Q) : Q := xiSpinGImage (xiSpinGammaImage q)

/-- The explicit image of the full seven-factor Norton word on every actual Q element. -/
noncomputable def monsterNortonUQImage (q : Q) : Q :=
  monsterSourceY82Image
    (sourceQCode 2049 1 *
      (sourceQCocode (golayLabelCoefficients 1807) *
        monsterNortonPermutationInverseImage 0
          (monsterNortonXiQImage
            (monsterNortonPermutationInverseImage 1 (monsterNortonXiQImage q))) *
        (sourceQCocode (golayLabelCoefficients 1807))⁻¹) * (sourceQCode 2049 1)⁻¹)

/-- Every central correction in that formula agrees with actual spin conjugation. -/
theorem monsterNortonUQImage_eq (q : Q) :
    spinConjugation monsterNortonUFiber.val.1 q = monsterNortonUQImage q := by
  rw [monsterNortonUFiber_spin]
  simp only [map_mul]
  change spinConjugation monsterSourceY82Spin
    (spinConjugation (spinHolomorphIncl (sourceQCode 2049 1))
      (spinConjugation (spinHolomorphIncl (sourceQCocode (golayLabelCoefficients 1807)))
        (spinConjugation (monsterSourcePermutationSpin 0)⁻¹
          (spinConjugation xiSpinHolomorph
            (spinConjugation (monsterSourcePermutationSpin 1)⁻¹
              (spinConjugation xiSpinHolomorph q)))))) = _
  rw [xiSpinHolomorph_conjugation, monsterNortonPermutationInverseImage_eq,
    xiSpinHolomorph_conjugation, monsterNortonPermutationInverseImage_eq,
    spinConjugation_incl, spinConjugation_incl, monsterSourceY82Spin_conjugation]
  rfl

/-- A finite recursive orbit with the actual full central phases retained. -/
noncomputable def monsterNortonQOrbit : ℕ → Q → Q
  | 0, q => q
  | n + 1, q => monsterNortonUQImage (monsterNortonQOrbit n q)

/-- Its recursive evaluation represents every natural power of actual u. -/
theorem monsterNortonQOrbit_eq (n : ℕ) (q : Q) :
    spinConjugation (monsterNortonUFiber ^ n).val.1 q = monsterNortonQOrbit n q := by
  induction n with
  | zero =>
    change spinConjugation 1 q = q
    rw [map_one]
    rfl
  | succ n ih =>
    rw [pow_succ']
    change spinConjugation (monsterNortonUFiber.val.1 * (monsterNortonUFiber ^ n).val.1) q = _
    rw [map_mul]
    change spinConjugation monsterNortonUFiber.val.1
      (spinConjugation (monsterNortonUFiber ^ n).val.1 q) = _
    rw [ih, monsterNortonUQImage_eq]
    rfl

/-- All point/line normal forms can be evaluated by the explicit finite orbit. -/
theorem monsterNortonPointLineQ_eq_orbit (i : Fin 13) (p : Q) :
    monsterNortonPointLineQ i p =
      monsterNortonQOrbit i.val (y555NortonVQ * p) * y555NortonVQ := by
  unfold monsterNortonPointLineQ
  rw [monsterNortonQOrbit_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
