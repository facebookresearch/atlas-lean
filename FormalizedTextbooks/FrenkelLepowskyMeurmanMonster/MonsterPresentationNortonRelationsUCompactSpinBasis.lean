/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Norton spin image of each basis vector has a proved sixty-four-term expansion. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinActual

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

private theorem six_factor_basis (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (u : SpinIndex) :
    (spinHolomorphIncl q * monsterMonomialDiagonalHolomorph M *
      monsterMonomialPermutationHolomorph P * xiSpinGHolomorph *
        monsterMonomialPermutationHolomorph R * monsterMonomialDiagonalHolomorph N).val
      (Pi.single u 1) = (1 / 8 : ℝ) •
      ∑ a : XiGrayIndex,
        (qSign (monsterMonomialQuadratic N u) * qSign (xiGrayQuadratic a) *
          qSign (monsterMonomialQuadratic M (P (R u + xiGrayCode a))) *
            qSign (spinPhase q (P (R u + xiGrayCode a) + spinTranslation q))) •
          (Pi.single (P (R u + xiGrayCode a) + spinTranslation q) 1 : SpinSpace) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change spinRepresentation q (monsterMonomialDiagonalEquiv M
    (monsterMonomialPermutation P (xiSpinG (monsterMonomialPermutation R
      (monsterMonomialDiagonalEquiv N (Pi.single u 1)))))) = _
  simp only [diagonal_basis, map_smul, permutation_basis, gaussian_basis,
    map_sum, smul_smul]
  simp only [q_basis, smul_smul]
  rw [mul_comm (qSign (monsterMonomialQuadratic N u)) (1 / 8 : ℝ), ← smul_smul]
  ext t
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply congrArg ((1 / 8 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual output label of one of the sixty-four spin basis transitions. -/
def monsterNortonUCompactBasisIndex (u : SpinIndex) (a : XiGrayIndex) : SpinIndex :=
  monsterNortonUCompactPermutation 0
    (monsterNortonUCompactPermutation 1 u + xiGrayCode a) +
      spinTranslation monsterNortonUCompactCorrection

/-- The complete integer sign of this genuine basis transition, including the global correction. -/
def monsterNortonUCompactBasisSign (u : SpinIndex) (a : XiGrayIndex) : ℤ :=
  -nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 1) u) *
    xiGraySign a *
      nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
        (monsterNortonUCompactPermutation 0
          (monsterNortonUCompactPermutation 1 u + xiGrayCode a))) *
        nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection
          (monsterNortonUCompactBasisIndex u a))

/-- Every actual Norton spin basis image is exactly the displayed sixty-four signed basis terms. -/
theorem monsterNortonUCompactSpin_actual_basis (u : SpinIndex) :
    monsterNortonUFiber.val.1.val (Pi.single u 1) = (1 / 8 : ℝ) •
      ∑ a : XiGrayIndex, (monsterNortonUCompactBasisSign u a : ℝ) •
        (Pi.single (monsterNortonUCompactBasisIndex u a) 1 : SpinSpace) := by
  rw [monsterNortonUCompactSpin_actual_apply]
  have h := six_factor_basis monsterNortonUCompactCorrection
    (monsterNortonUCompactDiagonal 0) (monsterNortonUCompactDiagonal 1)
      (monsterNortonUCompactPermutation 0) (monsterNortonUCompactPermutation 1) u
  change monsterNortonUCompactSpin.val (Pi.single u 1) = _ at h
  rw [h]
  ext t
  simp only [Pi.neg_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  apply congrArg ((1 / 8 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  simp only [monsterNortonUCompactBasisSign, Int.cast_mul, Int.cast_neg,
    nortonUIntegerSign_real, xiGraySign_real, monsterNortonUCompactBasisIndex]
  ring

/-- The same actual expansion uses the explicit published enumeration of sixty-four terms. -/
theorem monsterNortonUCompactSpin_actual_basis_fin64 (u : SpinIndex) :
    monsterNortonUFiber.val.1.val (Pi.single u 1) = (1 / 8 : ℝ) •
      ∑ a : Fin 64, (monsterNortonUCompactBasisSign u (monsterNortonGrayCoefficients a) : ℝ) •
        (Pi.single (monsterNortonUCompactBasisIndex u (monsterNortonGrayCoefficients a)) 1 :
          SpinSpace) := by
  rw [monsterNortonUCompactSpin_actual_basis]
  have hr := Equiv.sum_comp monsterNortonGrayEquiv (fun a : XiGrayIndex =>
    (monsterNortonUCompactBasisSign u a : ℝ) •
      (Pi.single (monsterNortonUCompactBasisIndex u a) 1 : SpinSpace))
  rw [← hr]
  rfl

/-- Outside those actual sixty-four output labels, every basis-image spin coordinate vanishes. -/
theorem monsterNortonUCompactSpin_basis_zero (u t : SpinIndex)
    (ht : ∀ a : XiGrayIndex, t ≠ monsterNortonUCompactBasisIndex u a) :
    monsterNortonUFiber.val.1.val (Pi.single u 1) t = 0 := by
  rw [monsterNortonUCompactSpin_actual_basis]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hterm (a : XiGrayIndex) : (monsterNortonUCompactBasisSign u a : ℝ) *
      (Pi.single (monsterNortonUCompactBasisIndex u a) 1 : SpinSpace) t = 0 := by
    simp [ht a]
  rw [Finset.sum_eq_zero (fun a _ => hterm a), mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
