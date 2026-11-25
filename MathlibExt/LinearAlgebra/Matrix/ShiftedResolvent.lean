/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Shifted resolvents and row-sum bounds

For a finite real matrix `K` and a parameter `λ > 0`, the fixed-point equation
`z = λ K (Y - z)` for a vector `z` is the linear system `(I + λ K) z = λ K Y`. When `K` is
positive semidefinite, `λ⁻¹ I + K` is invertible and the unique solution is the shifted
resolvent `z = (λ⁻¹ I + K)⁻¹ K Y = K (K + λ⁻¹ I)⁻¹ Y`. The fixed point and the linear system
are equivalent for every `K` and `λ`, and `K` commutes with `(c I + K)⁻¹` for every `c`;
positive semidefiniteness and `λ > 0` are what make the inverse a genuine inverse, so that
the fixed point is equivalent to the resolvent formula.

An entrywise nonnegative matrix whose row sums are at most `1` has spectral radius at most `1`:
its induced `∞` operator norm, the largest absolute row sum, is at most `1`. The spectral radius
is that of the complexified matrix, so nonreal eigenvalues of nonsymmetric matrices are
included. If the matrix is moreover symmetric its eigenvalues are real, and if it is positive
semidefinite they lie in `[0, 1]`. Nonnegativity with the row-sum bound gives the upper bound,
symmetry gives reality and positive semidefiniteness gives the lower bound; none of these
hypotheses can replace another.

The fitted values of kernel ridge regression with ridge `1 / λ` have the same matrix form
`K (K + λ⁻¹ I)⁻¹ Y` (`kernelRidgeFit_apply`). The statements here are finite matrix algebra
for an arbitrary positive semidefinite matrix: they do not identify `K` with the Gram matrix of
a particular kernel, nor a vector of fitted values with a function or with out-of-sample
predictions.

## Main results

* `fixedPoint_iff_shiftedResolvent`: the fixed point, the linear system and the shifted
  resolvent are equivalent for positive semidefinite `K` and `λ > 0`, and the two resolvent
  forms agree.
* `spectralRadius_le_one_of_rowSum_le_one`: nonnegative entries and row sums at most `1` give
  spectral radius at most `1`.
* `eigenvalues_mem_Icc_zero_one_of_rowSum_le_one`: a positive semidefinite matrix with
  nonnegative entries and row sums at most `1` has all eigenvalues in `[0, 1]`.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.ShiftedResolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `c • 1 + K` has invertible determinant for positive semidefinite `K` and `c > 0`. -/
private theorem isUnit_det_smul_one_add {K : Matrix n n ℝ} (hK : K.PosSemidef) {c : ℝ}
    (hc : 0 < c) : IsUnit (c • (1 : Matrix n n ℝ) + K).det := by
  rw [add_comm]
  exact (PosDef.posSemidef_add hK (PosDef.one.smul hc)).det_pos.ne'.isUnit

/-- The inverse of a matrix commutes with every matrix that the matrix commutes with. This uses
Mathlib's total inverse, which is `0` at a singular matrix, so it needs no invertibility. -/
private theorem inv_mul_comm_of_commute {A K : Matrix n n ℝ} (h : A * K = K * A) :
    A⁻¹ * K = K * A⁻¹ := by
  by_cases hA : IsUnit A.det
  · calc A⁻¹ * K = A⁻¹ * K * (A * A⁻¹) := by rw [mul_nonsing_inv _ hA, Matrix.mul_one]
      _ = A⁻¹ * (A * K) * A⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
      _ = K * A⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.one_mul]
  · simp [nonsing_inv_apply_not_isUnit _ hA]

/-- `K` commutes with its shifted inverse, for every shift `c`. -/
private theorem shiftedInv_mul_eq (K : Matrix n n ℝ) (c : ℝ) :
    (c • (1 : Matrix n n ℝ) + K)⁻¹ * K = K * (K + c • (1 : Matrix n n ℝ))⁻¹ := by
  rw [add_comm K]
  apply inv_mul_comm_of_commute
  rw [Matrix.add_mul, Matrix.mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
    Matrix.mul_one]

/-- The fixed-point equation is the linear system, for every `K` and `λ`. -/
private theorem fixedPoint_iff_linearSystem (K : Matrix n n ℝ) (lam : ℝ) (Y z : n → ℝ) :
    z = lam • (K *ᵥ (Y - z)) ↔ (1 + lam • K) *ᵥ z = lam • (K *ᵥ Y) := by
  rw [add_mulVec, one_mulVec, smul_mulVec, mulVec_sub, smul_sub]
  constructor <;> intro h
  · nth_rw 1 [h]; abel
  · rw [← h]; abel

/-- **Fixed point and shifted resolvent.** Let `K` be a positive semidefinite real matrix and
`λ > 0`. A vector `z` satisfies the fixed-point equation `z = λ K (Y - z)` if and only if it
solves the linear system `(I + λ K) z = λ K Y`, if and only if `z = (λ⁻¹ I + K)⁻¹ K Y`; and
`(λ⁻¹ I + K)⁻¹ K = K (K + λ⁻¹ I)⁻¹`. The first equivalence and the commutation hold for every
`K` and `λ`; positive semidefiniteness and `λ > 0` make `λ⁻¹ I + K` invertible, which the
equivalence with the resolvent formula needs. -/
theorem fixedPoint_iff_shiftedResolvent {K : Matrix n n ℝ} (hK : K.PosSemidef) {lam : ℝ}
    (hlam : 0 < lam) (Y z : n → ℝ) :
    (z = lam • (K *ᵥ (Y - z)) ↔ (1 + lam • K) *ᵥ z = lam • (K *ᵥ Y)) ∧
    (z = lam • (K *ᵥ (Y - z)) ↔ z = ((lam⁻¹ • (1 : Matrix n n ℝ) + K)⁻¹ * K) *ᵥ Y) ∧
    (lam⁻¹ • (1 : Matrix n n ℝ) + K)⁻¹ * K = K * (K + lam⁻¹ • (1 : Matrix n n ℝ))⁻¹ := by
  have e1 := fixedPoint_iff_linearSystem K lam Y z
  refine ⟨e1, ?_, shiftedInv_mul_eq K lam⁻¹⟩
  have hu := isUnit_det_smul_one_add hK (inv_pos.2 hlam)
  set A := lam⁻¹ • (1 : Matrix n n ℝ) + K
  have hA : (1 : Matrix n n ℝ) + lam • K = lam • A := by
    simp only [A, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  rw [e1, hA, smul_mulVec]
  constructor
  · intro h
    have h' : A *ᵥ z = K *ᵥ Y := by
      have := congrArg (fun w => lam⁻¹ • w) h
      simpa [smul_smul, inv_mul_cancel₀ hlam.ne'] using this
    rw [← mulVec_mulVec, ← h', mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  · intro h
    rw [h, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]

omit [DecidableEq n] in
/-- **Spectral radius under a row-sum bound.** A real matrix with nonnegative entries whose row
sums are all at most `1` has spectral radius at most `1`. The spectral radius is that of the
complexified matrix, so it bounds the modulus of every complex eigenvalue, including nonreal
eigenvalues of nonsymmetric matrices. The proof bounds it by the induced `∞` operator norm, the
largest absolute row sum. -/
theorem spectralRadius_le_one_of_rowSum_le_one [Nonempty n] {K : Matrix n n ℝ}
    (hnn : ∀ i j, 0 ≤ K i j) (hrow : ∀ i, ∑ j, K i j ≤ 1) :
    spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) ≤ 1 := by
  classical
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  have _ : NormOneClass (Matrix n n ℂ) := Matrix.linfty_opNormOneClass
  refine (spectralRadius_le_nnnorm _).trans ?_
  have : ‖K.map (algebraMap ℝ ℂ)‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    calc ∑ j, (‖(K.map (algebraMap ℝ ℂ)) i j‖₊ : ℝ) = ∑ j, K i j :=
          Finset.sum_congr rfl fun j _ => by
            simp [Real.norm_of_nonneg (hnn i j)]
      _ ≤ 1 := hrow i
  exact_mod_cast this

/-- Every real eigenvalue of a matrix with nonnegative entries and row sums at most `1` lies in
`[-1, 1]` (Gershgorin). -/
private theorem mem_Icc_of_mem_spectrum {K : Matrix n n ℝ} (hnn : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i, ∑ j, K i j ≤ 1) {μ : ℝ} (hμ : μ ∈ spectrum ℝ K) : μ ∈ Set.Icc (-1) 1 := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  rw [Metric.mem_closedBall, Real.dist_eq] at hk
  have hs : ∑ j ∈ Finset.univ.erase k, ‖K k j‖ = ∑ j ∈ Finset.univ.erase k, K k j :=
    Finset.sum_congr rfl fun j _ => Real.norm_of_nonneg (hnn k j)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => K k j) (Finset.mem_univ k)
  rw [hs] at hk
  have h1 := abs_le.1 hk
  have hr := hrow k
  have h0 := hnn k k
  have hsum0 : 0 ≤ ∑ j ∈ Finset.univ.erase k, K k j := Finset.sum_nonneg fun j _ => hnn k j
  constructor <;> linarith [h1.1, h1.2]

/-- The eigenvalues of a symmetric matrix with nonnegative entries and row sums at most `1` lie
in `[-1, 1]`. -/
private theorem eigenvalues_mem_Icc_neg_one_one {K : Matrix n n ℝ} (hS : K.IsHermitian)
    (hnn : ∀ i j, 0 ≤ K i j) (hrow : ∀ i, ∑ j, K i j ≤ 1) (i : n) :
    hS.eigenvalues i ∈ Set.Icc (-1) 1 :=
  mem_Icc_of_mem_spectrum hnn hrow (hS.eigenvalues_mem_spectrum_real i)

/-- **Eigenvalues under a row-sum bound.** The eigenvalues of a positive semidefinite real matrix
with nonnegative entries and row sums at most `1` lie in `[0, 1]`. Nonnegativity with the
row-sum bound gives the upper bound `1`, symmetry makes the eigenvalues real, and positive
semidefiniteness gives the lower bound `0`; positive semidefiniteness alone gives no upper
bound. -/
theorem eigenvalues_mem_Icc_zero_one_of_rowSum_le_one {K : Matrix n n ℝ} (hK : K.PosSemidef)
    (hnn : ∀ i j, 0 ≤ K i j) (hrow : ∀ i, ∑ j, K i j ≤ 1) (i : n) :
    hK.1.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hK.eigenvalues_nonneg i, (eigenvalues_mem_Icc_neg_one_one hK.1 hnn hrow i).2⟩

end MathlibExt.LinearAlgebra.Matrix.ShiftedResolvent
