/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sixty-four-term basis expansion of the genuine inverse Norton spin operator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinIndex

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open Multiplicative

private theorem add_right_eq (t u a : SpinIndex) : t + a = u ↔ t = u + a := by
  have ha : a + a = 0 := by
    ext j
    exact CharTwo.add_self_eq_zero (a j)
  constructor
  · intro h
    have hh := congrArg (fun x : SpinIndex => x + a) h
    simpa only [add_assoc, ha, add_zero] using hh
  · intro h
    rw [h, add_assoc, ha, add_zero]

private theorem diagonal_basis (M : Fin 12 → Fin 12 → ZMod 2) (u : SpinIndex) :
    monsterMonomialDiagonalEquiv M (Pi.single u 1) =
      qSign (monsterMonomialQuadratic M u) • (Pi.single u 1 : SpinSpace) := by
  ext t
  change qSign (monsterMonomialQuadratic M t) * (Pi.single u 1 : SpinSpace) t = _
  by_cases h : t = u
  · subst t
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
  · simp [h]

private theorem permutation_basis (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (u : SpinIndex) :
    monsterMonomialPermutation P (Pi.single u 1) = (Pi.single (P u) 1 : SpinSpace) := by
  ext t
  simp only [monsterMonomialPermutation_apply, Pi.single_apply, P.symm_apply_eq]

private theorem q_basis (q : Q) (u : SpinIndex) :
    spinRepresentation q (Pi.single u 1) =
      qSign (spinPhase q (u + spinTranslation q)) •
        (Pi.single (u + spinTranslation q) 1 : SpinSpace) := by
  ext t
  rw [monsterMonomialSpinRepresentation_apply]
  simp only [Pi.single_apply, add_right_eq, Pi.smul_apply, smul_eq_mul]
  by_cases h : t = u + spinTranslation q
  · simp only [h, ite_true]
  · simp only [h, ite_false, mul_zero]

private theorem gaussian_basis (u : SpinIndex) :
    xiSpinG (Pi.single u 1) = (1 / 8 : ℝ) •
      ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) •
        (Pi.single (u + xiGrayCode a) 1 : SpinSpace) := by
  ext t
  rw [nortonUIntegerG_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply congrArg ((1 / 8 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.single_apply, add_right_eq]

private theorem inverse_six_factor_basis (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (u : SpinIndex) :
    (monsterMonomialDiagonalHolomorph N * monsterMonomialPermutationHolomorph R *
      xiSpinGHolomorph * monsterMonomialPermutationHolomorph P *
        monsterMonomialDiagonalHolomorph M * spinHolomorphIncl q).val (Pi.single u 1) =
      (1 / 8 : ℝ) • ∑ a : XiGrayIndex,
        (qSign (spinPhase q (u + spinTranslation q)) *
          qSign (monsterMonomialQuadratic M (u + spinTranslation q)) *
          qSign (xiGrayQuadratic a) *
          qSign (monsterMonomialQuadratic N (R (P (u + spinTranslation q) + xiGrayCode a)))) •
            (Pi.single (R (P (u + spinTranslation q) + xiGrayCode a)) 1 : SpinSpace) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change monsterMonomialDiagonalEquiv N (monsterMonomialPermutation R
    (xiSpinG (monsterMonomialPermutation P (monsterMonomialDiagonalEquiv M
      (spinRepresentation q (Pi.single u 1)))))) = _
  simp only [q_basis, diagonal_basis, map_smul, permutation_basis, gaussian_basis,
    map_sum, smul_smul]
  ext t
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The genuine twelve-bit output of one inverse Gaussian basis transition. -/
def monsterNortonUCompactInverseBasisIndex (u : SpinIndex) (a : XiGrayIndex) : SpinIndex :=
  (monsterNortonUCompactPermutation 1).symm
    ((monsterNortonUCompactPermutation 0).symm
      (u + spinTranslation monsterNortonUCompactCorrection⁻¹) + xiGrayCode a)

/-- The complete inverse transition sign retains the resolved global phase and the inner Q phase. -/
def monsterNortonUCompactInverseBasisSign (u : SpinIndex) (a : XiGrayIndex) : ℤ :=
  -nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection⁻¹
      (u + spinTranslation monsterNortonUCompactCorrection⁻¹)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (u + spinTranslation monsterNortonUCompactCorrection⁻¹)) * xiGraySign a *
        nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 1)
          (monsterNortonUCompactInverseBasisIndex u a))

/-- Every genuine inverse spin basis image has sixty-four actual transitions. -/
theorem monsterNortonUCompactInverseSpin_actual_basis (u : SpinIndex) :
    (monsterNortonUFiber.val.1⁻¹).val (Pi.single u 1) = (1 / 8 : ℝ) •
      ∑ a : XiGrayIndex, (monsterNortonUCompactInverseBasisSign u a : ℝ) •
        (Pi.single (monsterNortonUCompactInverseBasisIndex u a) 1 : SpinSpace) := by
  rw [monsterNortonUCompactInverseSpin_actual_apply]
  have h := inverse_six_factor_basis monsterNortonUCompactCorrection⁻¹
    (monsterNortonUCompactDiagonal 0) (monsterNortonUCompactDiagonal 1)
      (monsterNortonUCompactPermutation 0).symm (monsterNortonUCompactPermutation 1).symm u
  change monsterNortonUCompactInverseSpin.val (Pi.single u 1) = _ at h
  rw [h]
  ext t
  simp only [Pi.neg_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  apply congrArg ((1 / 8 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  simp only [monsterNortonUCompactInverseBasisSign, Int.cast_mul, Int.cast_neg,
    nortonUIntegerSign_real, xiGraySign_real, monsterNortonUCompactInverseBasisIndex]
  ring

/-- The genuine inverse expansion also uses the explicit sixty-four-term enumeration. -/
theorem monsterNortonUCompactInverseSpin_actual_basis_fin64 (u : SpinIndex) :
    (monsterNortonUFiber.val.1⁻¹).val (Pi.single u 1) = (1 / 8 : ℝ) •
      ∑ a : Fin 64,
        (monsterNortonUCompactInverseBasisSign u (monsterNortonGrayCoefficients a) : ℝ) •
          (Pi.single (monsterNortonUCompactInverseBasisIndex u (monsterNortonGrayCoefficients a))
            1 : SpinSpace) := by
  rw [monsterNortonUCompactInverseSpin_actual_basis]
  have hr := Equiv.sum_comp monsterNortonGrayEquiv (fun a : XiGrayIndex =>
    (monsterNortonUCompactInverseBasisSign u a : ℝ) •
      (Pi.single (monsterNortonUCompactInverseBasisIndex u a) 1 : SpinSpace))
  rw [← hr]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
