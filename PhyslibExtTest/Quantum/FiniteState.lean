/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Quantum.FiniteState

/-!

# Tests for `PhyslibExt.Quantum.FiniteState`

Two-level checks of the Born rule, real expectation values, Kronecker products, operator domains
and the variational bound, with the boundary cases: the zero vector, a non-Hermitian matrix and a
function outside the momentum domain.

-/

@[expose] public section

namespace Quantum.FiniteState.Test

open Matrix
open scoped Kronecker

/-!

## Born probabilities

-/

/-- The two-level state `(1/√2, 1/√2)`. -/
noncomputable def plusState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(√2 : ℂ)⁻¹, (√2 : ℂ)⁻¹]

lemma inv_sqrt_two_sq : ((√2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma plusState_isNormalized : IsNormalized plusState := by
  rw [IsNormalized, EuclideanSpace.norm_eq]
  simp [plusState, Fin.sum_univ_two]
  norm_num

example : plusState ≠ 0 :=
  plusState_isNormalized.ne_zero

example (i : Fin 2) : bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) plusState i = 1 / 2 := by
  rw [bornProb, EuclideanSpace.basisFun_inner]
  fin_cases i <;> simp [plusState]

example : ∑ i, bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) plusState i = 1 :=
  sum_bornProb_eq_one _ plusState_isNormalized

example (i : Fin 2) :
    0 ≤ bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) plusState i ∧
      bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) plusState i ≤ 1 :=
  ⟨bornProb_nonneg _ _ i, bornProb_le_one _ plusState_isNormalized i⟩

/-- The unnormalized vector `(1, i)`. -/
def oneI : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![1, Complex.I]

example : ∑ i, bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) oneI i = 2 := by
  rw [sum_bornProb, EuclideanSpace.norm_sq_eq]
  simp [oneI, Fin.sum_univ_two]
  norm_num

example : ¬IsNormalized (0 : EuclideanSpace ℂ (Fin 2)) :=
  not_isNormalized_zero 2

example (b : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))) :
    ∑ i, bornProb b 0 i = 0 := by
  simp [bornProb]

example (b : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))) :
    ∑ i, bornProb b 0 i ≠ 1 := by
  simp [bornProb]

example : IsNormalized (Complex.I • plusState) :=
  plusState_isNormalized.smul (by simp)

example (i : Fin 2) :
    bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) (Complex.I • plusState) i =
      bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) plusState i :=
  bornProb_smul _ _ (by simp) i

/-!

## Adjoints and real expectation values

-/

/-- A Hermitian matrix with non-real off-diagonal entries. -/
def hermA : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.I; -Complex.I, 2]

lemma hermA_isHermitian : hermA.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermA]

example : hermAᴴ = hermA :=
  hermA_isHermitian.eq

lemma inner_plusState_hermA :
    inner ℂ plusState (WithLp.toLp 2 (hermA *ᵥ plusState.ofLp)) = 3 / 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, plusState, hermA, dotProduct, Fin.sum_univ_two]
  linear_combination (3 : ℂ) * inv_sqrt_two_sq

example : expectationValue hermA plusState = 3 / 2 := by
  rw [expectationValue, inner_plusState_hermA]
  norm_num

example : inner ℂ plusState (WithLp.toLp 2 (hermA *ᵥ plusState.ofLp)) =
    (expectationValue hermA plusState : ℂ) :=
  inner_mulVec_self_eq_expectationValue hermA_isHermitian plusState

example (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (WithLp.toLp 2 (hermA *ᵥ x.ofLp)) y = inner ℂ x (WithLp.toLp 2 (hermA *ᵥ y.ofLp)) :=
  inner_mulVec_left_of_isHermitian hermA_isHermitian x y

/-- A non-Hermitian matrix. -/
def nonHerm : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

example (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (WithLp.toLp 2 (nonHerm *ᵥ x.ofLp)) y =
      inner ℂ x (WithLp.toLp 2 (nonHermᴴ *ᵥ y.ofLp)) :=
  inner_mulVec_left nonHerm x y

example : ¬nonHerm.IsHermitian := by
  intro h
  simpa [nonHerm] using congrFun (congrFun h 0) 1

lemma im_inner_oneI_nonHerm : (inner ℂ oneI (WithLp.toLp 2 (nonHerm *ᵥ oneI.ofLp))).im = 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, oneI, nonHerm, dotProduct, Fin.sum_univ_two]

example : (inner ℂ oneI (WithLp.toLp 2 (nonHerm *ᵥ oneI.ofLp))).im ≠ 0 := by
  rw [im_inner_oneI_nonHerm]
  exact one_ne_zero

/-!

## Kronecker products

-/

/-- The Pauli matrix `σ_x`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The Pauli matrix `σ_y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

lemma pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

lemma pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY]

example : (pauliX ⊗ₖ pauliY)ᴴ = pauliXᴴ ⊗ₖ pauliYᴴ :=
  conjTranspose_kronecker pauliX pauliY

example : (pauliX ⊗ₖ pauliY).IsHermitian :=
  isHermitian_kronecker pauliX_isHermitian pauliY_isHermitian

example : (pauliX ⊗ₖ pauliY) (0, 0) (1, 1) = -Complex.I := by
  simp [pauliX, pauliY]

/-!

## Operators with domains

-/

example : (fun x : ℝ => ((|x| : ℝ) : ℂ)) ∉ momentumOperator.domain :=
  abs_notMem_momentumOperator_domain

example : momentumOperator.domain ⊂ Set.univ :=
  momentumOperator_domain_ssubset_univ

example : Function.Injective momentumOperator.embedding :=
  OperatorWithDomain.embedding_injective _

example : (fun _ : ℝ => (1 : ℂ)) ∈ momentumOperator.domain :=
  const_one_mem_momentumOperator_domain

example : (fun _ : ℝ => (1 : ℂ)) ∈ (differentialHamiltonian fun x => ((x ^ 2 : ℝ) : ℂ)).domain :=
  const_one_mem_differentialHamiltonian_domain _

example (f : ℝ → ℂ) : f ∈ positionOperator.domain := by
  rw [positionOperator_domain]
  exact Set.mem_univ f

example : positionOperator.op ⟨fun _ => 1, Set.mem_univ _⟩ = fun x : ℝ => (x : ℂ) := by
  funext x
  simp [positionOperator]

example : momentumOperator.op ⟨fun _ => 1, const_one_mem_momentumOperator_domain⟩ = 0 := by
  funext x
  simp [momentumOperator]

example (V : ℝ → ℂ) :
    (differentialHamiltonian V).op ⟨fun _ => 1, const_one_mem_differentialHamiltonian_domain V⟩ =
      V := by
  funext x
  simp [differentialHamiltonian]

/-!

## Variational bound

-/

/-- The rotation with cosine `3/5` and sine `4/5`. -/
noncomputable def rotation : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 / 5, -4 / 5; 4 / 5, 3 / 5]

/-- The eigenvalues `1` and `-1`. -/
def eigs : Fin 2 → ℝ :=
  ![1, -1]

/-- The Hermitian matrix `rotation * diagonal eigs * rotationᴴ`. -/
noncomputable def varMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-7 / 25, 24 / 25; 24 / 25, 7 / 25]

lemma rotation_mem_unitaryGroup : rotation ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, mul_apply, Fin.sum_univ_two, Complex.conj_ofNat] <;> norm_num

lemma varMatrix_eq : varMatrix = rotation * diagonal (fun i => (eigs i : ℂ)) * rotationᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [varMatrix, rotation, eigs, mul_apply, vecMul_diagonal, Fin.sum_univ_two,
      Complex.conj_ofNat] <;> norm_num

example : varMatrix.IsHermitian := by
  rw [varMatrix_eq]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [Complex.conj_ofReal]))

lemma inf'_eigs : Finset.univ.inf' Finset.univ_nonempty eigs = -1 :=
  le_antisymm ((Finset.inf'_le eigs (Finset.mem_univ 1)).trans_eq (by simp [eigs]))
    (Finset.le_inf' _ _ fun i _ => by fin_cases i <;> norm_num [eigs])

example {ψ : EuclideanSpace ℂ (Fin 2)} (hψ : IsNormalized ψ) :
    -1 ≤ expectationValue varMatrix ψ := by
  simpa [inf'_eigs] using inf'_le_expectationValue rotation_mem_unitaryGroup varMatrix_eq hψ

/-- The eigenvector `(-4/5, 3/5)` of `varMatrix` for the eigenvalue `-1`. -/
noncomputable def minState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![-4 / 5, 3 / 5]

example : IsNormalized minState := by
  rw [IsNormalized, EuclideanSpace.norm_eq]
  simp [minState, Fin.sum_univ_two]
  norm_num

example : expectationValue varMatrix minState = -1 := by
  simp [expectationValue, EuclideanSpace.inner_eq_star_dotProduct, varMatrix, minState,
    dotProduct, Fin.sum_univ_two, Complex.conj_ofNat]
  norm_num

example {ψ : EuclideanSpace ℂ (Fin 2)} (hψ : IsNormalized ψ) :
    Finset.univ.inf' Finset.univ_nonempty pauliX_isHermitian.eigenvalues ≤
      expectationValue pauliX ψ :=
  inf'_eigenvalues_le_expectationValue pauliX_isHermitian hψ

/-!

## Axioms

-/

#print axioms not_isNormalized_zero
#print axioms IsNormalized.ne_zero
#print axioms IsNormalized.smul
#print axioms bornProb_nonneg
#print axioms sum_bornProb
#print axioms sum_bornProb_eq_one
#print axioms bornProb_le_one
#print axioms bornProb_smul
#print axioms inner_mulVec_left
#print axioms inner_mulVec_left_of_isHermitian
#print axioms im_inner_mulVec_self_eq_zero
#print axioms inner_mulVec_self_eq_expectationValue
#print axioms isHermitian_kronecker
#print axioms OperatorWithDomain.embedding_injective
#print axioms positionOperator_domain
#print axioms abs_notMem_momentumOperator_domain
#print axioms momentumOperator_domain_ssubset_univ
#print axioms const_one_mem_momentumOperator_domain
#print axioms const_one_mem_differentialHamiltonian_domain
#print axioms inf'_le_expectationValue
#print axioms inf'_eigenvalues_le_expectationValue

end Quantum.FiniteState.Test
