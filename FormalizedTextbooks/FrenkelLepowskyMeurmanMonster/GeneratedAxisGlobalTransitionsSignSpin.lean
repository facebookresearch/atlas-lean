/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddTheta

/-! The quadratic and shear spin operator prescribed by the actual opposite-source Fourier rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The literal linear theta character as a diagonal binary quadratic matrix. -/
def generatedAxisGlobalSignLinearPhase (a : Fin 2048) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => if i = j then sourceCodeThetaPolynomial (monsterNortonYCode a) i else 0

/-- The full opposite-source quadratic phase, including its additional linear theta terms. -/
def generatedAxisGlobalSignPhaseMatrix (a : Fin 2048) : Fin 12 → Fin 12 → ZMod 2 :=
  monsterSourceYPhaseMatrix (monsterNortonYCode a) + generatedAxisGlobalSignLinearPhase a

/-- The diagonal polynomial is exactly its literal linear source theta character. -/
theorem generatedAxisGlobalSignLinearPhase_apply (a : Fin 2048) (t : SpinIndex) :
    monsterMonomialQuadratic (generatedAxisGlobalSignLinearPhase a) t =
      spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) t := by
  have hb : ∀ z : ZMod 2, z * z = z := by decide +kernel
  simp only [monsterMonomialQuadratic, generatedAxisGlobalSignLinearPhase,
    mul_ite, mul_zero, Fintype.sum_ite_eq, hb]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The prescribed quadratic matrix has exactly the two Fourier-sector source phases. -/
theorem generatedAxisGlobalSignPhaseMatrix_apply (a : Fin 2048) (t : SpinIndex) :
    monsterMonomialQuadratic (generatedAxisGlobalSignPhaseMatrix a) t =
      spinDot (sourceCodeThetaPolynomial t) (monsterNortonYCode a) +
        (1 + t 11) * spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) t := by
  rw [generatedAxisGlobalSignPhaseMatrix, monsterMonomialQuadratic_matrix_add,
    monsterSourceYPhaseMatrix_apply, generatedAxisGlobalSignLinearPhase_apply]
  ring

/-- The exact quadratic sign and actual binary shear in the original Fourier coordinates. -/
def generatedAxisGlobalSignPlusMinus (a : Fin 2048) : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph (generatedAxisGlobalSignPhaseMatrix a) *
    monsterMonomialPermutationHolomorph (monsterNortonYShear a)

/-- Every Fourier output has its literal quadratic phase and source shear label. -/
theorem generatedAxisGlobalSignPlusMinus_apply (a : Fin 2048) (f : SpinSpace) (t : SpinIndex) :
    (generatedAxisGlobalSignPlusMinus a).val f t =
      qSign (spinDot (sourceCodeThetaPolynomial t) (monsterNortonYCode a) +
        (1 + t 11) * spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) t) *
          f (t + t 11 • monsterNortonYCode a) := by
  change qSign (monsterMonomialQuadratic (generatedAxisGlobalSignPhaseMatrix a) t) *
    f ((monsterNortonYShear a).symm t) = _
  rw [generatedAxisGlobalSignPhaseMatrix_apply, monsterNortonYShear_symm]
  rfl

/-- The prescribed spin operator is the genuine Hadamard conjugate of these source factors. -/
def generatedAxisGlobalSignSpin (a : Fin 2048) : SpinHolomorph :=
  monsterSpinHadamardHolomorph * generatedAxisGlobalSignPlusMinus a * monsterSpinHadamardHolomorph

/-- The explicit extraspecial image includes every Fourier and quadratic central correction. -/
def generatedAxisGlobalSignSpinImage (a : Fin 2048) (q : Q) : Q :=
  monsterSpinHadamardImage
    (monsterMonomialDiagonalImage (generatedAxisGlobalSignPhaseMatrix a)
      (monsterMonomialPermutationImage (monsterNortonYShear a) (monsterSpinHadamardImage q)))

/-- All displayed factors give exactly their genuine complete Q conjugation. -/
theorem generatedAxisGlobalSignSpin_conjugation (a : Fin 2048) (q : Q) :
    spinConjugation (generatedAxisGlobalSignSpin a) q = generatedAxisGlobalSignSpinImage a q := by
  rw [generatedAxisGlobalSignSpin, generatedAxisGlobalSignPlusMinus, map_mul, map_mul, map_mul]
  change spinConjugation monsterSpinHadamardHolomorph
    (spinConjugation (monsterMonomialDiagonalHolomorph (generatedAxisGlobalSignPhaseMatrix a))
      (spinConjugation (monsterMonomialPermutationHolomorph (monsterNortonYShear a))
        (spinConjugation monsterSpinHadamardHolomorph q))) = _
  rw [monsterSpinHadamardHolomorph_conjugation, monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, monsterSpinHadamardHolomorph_conjugation]
  rfl

/-- The spin operator has exactly the prescribed Fourier-coordinate action. -/
theorem generatedAxisGlobalSignSpin_fourier (a : Fin 2048) (f : SpinSpace) :
    monsterSpinHadamard ((generatedAxisGlobalSignSpin a).val f) =
      (generatedAxisGlobalSignPlusMinus a).val (monsterSpinHadamard f) := by
  change monsterSpinHadamard (monsterSpinHadamard
    ((generatedAxisGlobalSignPlusMinus a).val (monsterSpinHadamard f))) = _
  exact monsterSpinHadamard_involutive _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
