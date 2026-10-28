/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sixteen-term basis expansion of the genuine inverse Norton spin operator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoGaussianCoordinates

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
    monsterNortonUTwoGaussian (Pi.single u 1) = (1 / 4 : ℝ) •
      ∑ a : Fin 16, qSign (monsterNortonUTwoGaussianQuadratic a) •
        (Pi.single (u + golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel a)) 1 :
          SpinSpace) := by
  ext t
  rw [monsterNortonUTwoGaussian_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply congrArg ((1 / 4 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.single_apply, add_right_eq]

private theorem inverse_six_factor_basis (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (u : SpinIndex) :
    (monsterMonomialDiagonalHolomorph N * monsterMonomialPermutationHolomorph R *
      monsterNortonUTwoGaussianHolomorph * monsterMonomialPermutationHolomorph P *
        monsterMonomialDiagonalHolomorph M * spinHolomorphIncl q).val (Pi.single u 1) =
      (1 / 4 : ℝ) • ∑ a : Fin 16,
        (qSign (spinPhase q (u + spinTranslation q)) *
          qSign (monsterMonomialQuadratic M (u + spinTranslation q)) *
          qSign (monsterNortonUTwoGaussianQuadratic a) *
          qSign (monsterMonomialQuadratic N (R (P (u + spinTranslation q) +
            golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel a))))) •
            (Pi.single (R (P (u + spinTranslation q) + golayLabelCoefficients
              (monsterNortonUTwoGaussianSpinLabel a))) 1 : SpinSpace) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change monsterMonomialDiagonalEquiv N (monsterMonomialPermutation R
    (monsterNortonUTwoGaussian (monsterMonomialPermutation P (monsterMonomialDiagonalEquiv M
      (spinRepresentation q (Pi.single u 1)))))) = _
  simp only [q_basis, diagonal_basis, map_smul, permutation_basis, gaussian_basis,
    map_sum, smul_smul]
  ext t
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The genuine twelve-bit output of one inverse Gaussian basis transition. -/
def monsterNortonUTwoCompactInverseBasisIndex (u : SpinIndex) (a : Fin 16) : SpinIndex :=
  (monsterNortonUTwoCompactPermutation 1).symm
    ((monsterNortonUTwoCompactPermutation 0).symm
      (u + spinTranslation monsterNortonUTwoCompactCorrection⁻¹) + golayLabelCoefficients
        (monsterNortonUTwoGaussianSpinLabel a))

/-- The complete inverse transition sign retains the resolved global phase and the inner Q phase. -/
def monsterNortonUTwoCompactInverseBasisSign (u : SpinIndex) (a : Fin 16) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUTwoCompactCorrection⁻¹
      (u + spinTranslation monsterNortonUTwoCompactCorrection⁻¹)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUTwoCompactDiagonal 0)
      (u + spinTranslation monsterNortonUTwoCompactCorrection⁻¹)) *
        monsterNortonUTwoGaussianSign a *
        nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUTwoCompactDiagonal 1)
          (monsterNortonUTwoCompactInverseBasisIndex u a))

/-- Every genuine inverse spin basis image has sixteen actual transitions. -/
theorem monsterNortonUTwoCompactInverseSpin_actual_basis (u : SpinIndex) :
    ((monsterNortonUFiber.val.1 ^ 2)⁻¹).val (Pi.single u 1) = (1 / 4 : ℝ) •
      ∑ a : Fin 16, (monsterNortonUTwoCompactInverseBasisSign u a : ℝ) •
        (Pi.single (monsterNortonUTwoCompactInverseBasisIndex u a) 1 : SpinSpace) := by
  rw [monsterNortonUTwoCompactSpin_actual, monsterNortonUTwoCompactInverseSpin_eq]
  have h := inverse_six_factor_basis monsterNortonUTwoCompactCorrection⁻¹
    (monsterNortonUTwoCompactDiagonal 0) (monsterNortonUTwoCompactDiagonal 1)
      (monsterNortonUTwoCompactPermutation 0).symm (monsterNortonUTwoCompactPermutation 1).symm u
  change monsterNortonUTwoCompactInverseSpin.val (Pi.single u 1) = _ at h
  rw [h]
  ext t
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply congrArg ((1 / 4 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  simp only [monsterNortonUTwoCompactInverseBasisSign, Int.cast_mul,
    nortonUIntegerSign_real, monsterNortonUTwoGaussianSign_real,
    monsterNortonUTwoCompactInverseBasisIndex]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
