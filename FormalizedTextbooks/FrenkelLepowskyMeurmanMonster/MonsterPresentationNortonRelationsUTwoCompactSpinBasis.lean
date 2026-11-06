/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Norton spin image of each basis vector has a proved sixteen-term expansion. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinActual
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

private theorem six_factor_basis (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (u : SpinIndex) :
    (spinHolomorphIncl q * monsterMonomialDiagonalHolomorph M *
      monsterMonomialPermutationHolomorph P * monsterNortonUTwoGaussianHolomorph *
        monsterMonomialPermutationHolomorph R * monsterMonomialDiagonalHolomorph N).val
      (Pi.single u 1) = (1 / 4 : ℝ) •
      ∑ a : Fin 16,
        (qSign (monsterMonomialQuadratic N u) * qSign (monsterNortonUTwoGaussianQuadratic a) *
          qSign (monsterMonomialQuadratic M (P (R u + golayLabelCoefficients
            (monsterNortonUTwoGaussianSpinLabel a)))) *
            qSign (spinPhase q (P (R u + golayLabelCoefficients
              (monsterNortonUTwoGaussianSpinLabel a)) + spinTranslation q))) •
          (Pi.single (P (R u + golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel a))
            + spinTranslation q) 1 : SpinSpace) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change spinRepresentation q (monsterMonomialDiagonalEquiv M
    (monsterMonomialPermutation P (monsterNortonUTwoGaussian (monsterMonomialPermutation R
      (monsterMonomialDiagonalEquiv N (Pi.single u 1)))))) = _
  simp only [diagonal_basis, map_smul, permutation_basis, gaussian_basis,
    map_sum, smul_smul]
  simp only [q_basis, smul_smul]
  rw [mul_comm (qSign (monsterMonomialQuadratic N u)) (1 / 4 : ℝ), ← smul_smul]
  ext t
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply congrArg ((1 / 4 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual output label of one of the sixteen spin basis transitions. -/
def monsterNortonUTwoCompactBasisIndex (u : SpinIndex) (a : Fin 16) : SpinIndex :=
  monsterNortonUTwoCompactPermutation 0
    (monsterNortonUTwoCompactPermutation 1 u + golayLabelCoefficients
      (monsterNortonUTwoGaussianSpinLabel a)) +
      spinTranslation monsterNortonUTwoCompactCorrection

/-- The complete integer sign of this genuine basis transition, including the global correction. -/
def monsterNortonUTwoCompactBasisSign (u : SpinIndex) (a : Fin 16) : ℤ :=
  nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUTwoCompactDiagonal 1) u) *
    monsterNortonUTwoGaussianSign a *
      nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUTwoCompactDiagonal 0)
        (monsterNortonUTwoCompactPermutation 0
          (monsterNortonUTwoCompactPermutation 1 u + golayLabelCoefficients
            (monsterNortonUTwoGaussianSpinLabel a)))) *
        nortonUIntegerSign (spinPhase monsterNortonUTwoCompactCorrection
          (monsterNortonUTwoCompactBasisIndex u a))

/-- Every actual Norton spin basis image is exactly the displayed sixteen signed basis terms. -/
theorem monsterNortonUTwoCompactSpin_actual_basis (u : SpinIndex) :
    (monsterNortonUFiber.val.1 ^ 2).val (Pi.single u 1) = (1 / 4 : ℝ) •
      ∑ a : Fin 16, (monsterNortonUTwoCompactBasisSign u a : ℝ) •
        (Pi.single (monsterNortonUTwoCompactBasisIndex u a) 1 : SpinSpace) := by
  rw [monsterNortonUTwoCompactSpin_actual]
  have h := six_factor_basis monsterNortonUTwoCompactCorrection
    (monsterNortonUTwoCompactDiagonal 0) (monsterNortonUTwoCompactDiagonal 1)
      (monsterNortonUTwoCompactPermutation 0) (monsterNortonUTwoCompactPermutation 1) u
  change monsterNortonUTwoCompactSpin.val (Pi.single u 1) = _ at h
  rw [h]
  ext t
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply congrArg ((1 / 4 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  simp only [monsterNortonUTwoCompactBasisSign, Int.cast_mul,
    nortonUIntegerSign_real, monsterNortonUTwoGaussianSign_real,
    monsterNortonUTwoCompactBasisIndex]

/-- Outside those actual sixteen output labels, every basis-image spin coordinate vanishes. -/
theorem monsterNortonUTwoCompactSpin_basis_zero (u t : SpinIndex)
    (ht : ∀ a : Fin 16, t ≠ monsterNortonUTwoCompactBasisIndex u a) :
    (monsterNortonUFiber.val.1 ^ 2).val (Pi.single u 1) t = 0 := by
  rw [monsterNortonUTwoCompactSpin_actual_basis]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hterm (a : Fin 16) : (monsterNortonUTwoCompactBasisSign u a : ℝ) *
      (Pi.single (monsterNortonUTwoCompactBasisIndex u a) 1 : SpinSpace) t = 0 := by
    simp [ht a]
  rw [Finset.sum_eq_zero (fun a _ => hterm a), mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
