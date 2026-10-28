/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full quadratic phase in the source y-code spin action, from Seysen Table 3. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinHadamardNormalizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The linear theta terms represented as a binary diagonal quadratic matrix. -/
def monsterSourceYLinearMatrix (e : SpinIndex) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => if i = j then ∑ k, sourceCodeTheta i k * e k else 0

/-- The actual associator terms of theta, retaining the published basis coefficients. -/
def monsterSourceYThetaMatrix (e : SpinIndex) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => if i < j then ∑ k,
    golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) * e k else 0

/-- The last-coordinate correction distinguishing the source plus/minus spin spaces. -/
def monsterSourceYLastMatrix (e : SpinIndex) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => if i = 11 then sourceCodeThetaPolynomial e j else 0

/-- The exact quadratic matrix for the source y-code phase in the plus/minus basis. -/
def monsterSourceYPhaseMatrix (e : SpinIndex) : Fin 12 → Fin 12 → ZMod 2 :=
  monsterSourceYLinearMatrix e + monsterSourceYThetaMatrix e + monsterSourceYLastMatrix e

/-- Adding binary coefficient matrices adds their actual quadratic polynomials. -/
theorem monsterMonomialQuadratic_matrix_add (M N : Fin 12 → Fin 12 → ZMod 2)
    (a : SpinIndex) : monsterMonomialQuadratic (M + N) a =
      monsterMonomialQuadratic M a + monsterMonomialQuadratic N a := by
  simp only [monsterMonomialQuadratic, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Binary diagonal terms evaluate as linear terms, with no assumed phase equation. -/
theorem monsterSourceYLinearMatrix_apply (e a : SpinIndex) :
    monsterMonomialQuadratic (monsterSourceYLinearMatrix e) a =
      ∑ i, a i * ∑ k, sourceCodeTheta i k * e k := by
  have hs : ∀ z : ZMod 2, z * z = z := by decide +kernel
  simp only [monsterMonomialQuadratic, monsterSourceYLinearMatrix, mul_ite, mul_zero,
    Fintype.sum_ite_eq, hs]

/-- The associator coefficients evaluate by their exact upper triangular sum. -/
theorem monsterSourceYThetaMatrix_apply (e a : SpinIndex) :
    monsterMonomialQuadratic (monsterSourceYThetaMatrix e) a =
      ∑ i, ∑ j, if i < j then a i * a j * ∑ k,
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) * e k else 0 := by
  simp only [monsterMonomialQuadratic, monsterSourceYThetaMatrix, mul_ite, mul_zero]

/-- The last-coordinate correction evaluates to its literal source character. -/
theorem monsterSourceYLastMatrix_apply (e a : SpinIndex) :
    monsterMonomialQuadratic (monsterSourceYLastMatrix e) a =
      a 11 * spinDot (sourceCodeThetaPolynomial e) a := by
  simp only [monsterMonomialQuadratic, monsterSourceYLastMatrix, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']
  simp only [spinDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact sum reindexing expands the source theta character into its linear and quadratic terms. -/
theorem monsterSourceY_theta_expansion (e a : SpinIndex) :
    spinDot (sourceCodeThetaPolynomial a) e =
      (∑ i, a i * ∑ k, sourceCodeTheta i k * e k) +
        ∑ i, ∑ j, if i < j then a i * a j * ∑ k,
          golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) * e k else 0 := by
  simp only [spinDot, sourceCodeThetaPolynomial, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul]
  apply congrArg₂ (fun x y : ZMod 2 => x + y)
  · rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [h, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp only [h, ite_false, zero_mul, Finset.sum_const_zero]

/-- The actual coefficient matrix computes the full primary source y-code phase on every label. -/
theorem monsterSourceYPhaseMatrix_apply (e a : SpinIndex) :
    monsterMonomialQuadratic (monsterSourceYPhaseMatrix e) a =
      spinDot (sourceCodeThetaPolynomial a) e +
        a 11 * spinDot (sourceCodeThetaPolynomial e) a := by
  rw [monsterSourceYPhaseMatrix, monsterMonomialQuadratic_matrix_add,
    monsterMonomialQuadratic_matrix_add, monsterSourceYLinearMatrix_apply,
    monsterSourceYThetaMatrix_apply, monsterSourceYLastMatrix_apply,
    ← monsterSourceY_theta_expansion]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
