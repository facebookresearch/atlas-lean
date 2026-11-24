/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Neumann series for a contractive input–output matrix

Let `A` be a nonnegative input–output matrix whose row sums are all below `1`; for nonnegative
`A` this is the explicit operator-norm contraction bound `‖A‖ < 1` for the `ℓ∞` operator norm
(`Matrix.linftyOpNormedRing`). Then `1 - A` is invertible
(`isUnit_one_sub_of_rowSum_lt_one`), the Neumann series `∑ n, A ^ n` converges to the
Leontief inverse `(1 - A)⁻¹` (`hasSum_pow_of_rowSum_lt_one`), and the Leontief inverse is
entrywise nonnegative (`inv_one_sub_nonneg_of_rowSum_lt_one`).

The statements use only the standard topology on matrices; the `ℓ∞` operator norm is
activated locally in the proofs. `Matrix.inv_one_sub_nonneg` gives nonnegativity under the
weaker hypothesis that the spectral radius is below `1`. A row sum equal to `1` (a closed
production loop) can make `1 - A` singular.

Orientation: `A i j` is the input of sector `i` per unit of sector `j`'s output (the usual
technical-coefficient convention), and the bound is on row sums `∑ j, A i j`. The common
column-sum condition `∑ i, A i j < 1` is the same statement for `Aᵀ`, since
`(1 - Aᵀ)⁻¹ = ((1 - A)⁻¹)ᵀ`.

## References

* R. E. Miller, P. D. Blair, *Input-Output Analysis: Foundations and Extensions*, 2nd ed.,
  Cambridge University Press (2009), Chapter 2 (the Leontief inverse and its power-series
  approximation `I + A + A² + ⋯`).
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Section 5.6 (convergent Neumann series when a matrix norm of `A` is below `1`).

## Main results

* `MathlibExt.Economics.InputOutput.isUnit_one_sub_of_rowSum_lt_one`
* `MathlibExt.Economics.InputOutput.hasSum_pow_of_rowSum_lt_one`
* `MathlibExt.Economics.InputOutput.inv_one_sub_nonneg_of_rowSum_lt_one`

Atlas roadmap target AP06.T02.
-/

namespace MathlibExt.Economics.InputOutput

open Matrix

/-- **Contraction bound gives invertibility.** If the nonnegative input matrix `A` has every
row sum below `1` (its `ℓ∞` operator norm is `< 1`), then `1 - A` is invertible. -/
theorem isUnit_one_sub_of_rowSum_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j < 1) :
    IsUnit (1 - A) := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  let _ : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ (Matrix ι ι ℝ)
  have hnorm : ‖A‖ < 1 := by
    have hnorm_eq : ‖A‖ = ↑((Finset.univ : Finset ι).sup fun i => ∑ j, ‖A i j‖₊) :=
      Matrix.linfty_opNorm_def A
    rw [hnorm_eq, ← NNReal.coe_one, NNReal.coe_lt_coe]
    rw [Finset.sup_lt_iff (by simp : (⊥ : NNReal) < 1)]
    intro i _
    rw [← NNReal.coe_lt_coe, NNReal.coe_sum, NNReal.coe_one]
    simp_rw [coe_nnnorm, show ∀ j, ‖A i j‖ = A i j from fun j => Real.norm_of_nonneg (hA0 i j)]
    exact hrow i
  exact ⟨Units.mk _ _ (mul_neg_geom_series A hnorm) (geom_series_mul_neg A hnorm), rfl⟩

/-- **Neumann series.** Under the same row-sum contraction bound, the power series
`∑ n, A ^ n` converges (entrywise) to the Leontief inverse `(1 - A)⁻¹`. -/
theorem hasSum_pow_of_rowSum_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j < 1) :
    HasSum (fun n : ℕ => A ^ n) (1 - A)⁻¹ := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  let _ : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ (Matrix ι ι ℝ)
  have hnorm : ‖A‖ < 1 := by
    have hnorm_eq : ‖A‖ = ↑((Finset.univ : Finset ι).sup fun i => ∑ j, ‖A i j‖₊) :=
      Matrix.linfty_opNorm_def A
    rw [hnorm_eq, ← NNReal.coe_one, NNReal.coe_lt_coe]
    rw [Finset.sup_lt_iff (by simp : (⊥ : NNReal) < 1)]
    intro i _
    rw [← NNReal.coe_lt_coe, NNReal.coe_sum, NNReal.coe_one]
    simp_rw [coe_nnnorm, show ∀ j, ‖A i j‖ = A i j from fun j => Real.norm_of_nonneg (hA0 i j)]
    exact hrow i
  have hsum_mat : HasSum (fun n : ℕ => A ^ n) (∑' n : ℕ, A ^ n) :=
    (summable_geometric_of_norm_lt_one hnorm).hasSum
  have hinv : (1 - A)⁻¹ = ∑' n : ℕ, A ^ n :=
    Matrix.inv_eq_right_inv (mul_neg_geom_series A hnorm)
  have hbound : ∀ (M : Matrix ι ι ℝ) (i j : ι), ‖M i j‖ ≤ 1 * ‖M‖ := by
    intro M i j
    rw [one_mul]
    have hnorm_eq : ‖M‖ = ↑((Finset.univ : Finset ι).sup fun i => ∑ j, ‖M i j‖₊) :=
      Matrix.linfty_opNorm_def M
    rw [hnorm_eq, ← coe_nnnorm]
    norm_cast
    calc ‖M i j‖₊ ≤ ∑ j', ‖M i j'‖₊ :=
            Finset.single_le_sum (f := fun j' => ‖M i j'‖₊) (fun j' _ => zero_le)
              (Finset.mem_univ j)
      _ ≤ (Finset.univ : Finset ι).sup fun i => ∑ j, ‖M i j‖₊ :=
            Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have hentry : ∀ i j, HasSum (fun n : ℕ => (A ^ n) i j) ((1 - A)⁻¹ i j) := by
    intro i j
    rw [hinv]
    let hφ := LinearMap.mkContinuous
      ({ toFun := fun M : Matrix ι ι ℝ => M i j
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : (Matrix ι ι ℝ) →ₗ[ℝ] ℝ)
      1 (fun M => hbound M i j)
    exact hφ.hasSum hsum_mat
  exact Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => hentry i j

/-- **Nonnegative Leontief inverse.** Under the same bound, every entry of `(1 - A)⁻¹` is
nonnegative. -/
theorem inv_one_sub_nonneg_of_rowSum_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j < 1) (i j : ι) :
    0 ≤ (1 - A)⁻¹ i j := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  let _ : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ (Matrix ι ι ℝ)
  have hnorm : ‖A‖ < 1 := by
    have hnorm_eq : ‖A‖ = ↑((Finset.univ : Finset ι).sup fun i => ∑ j, ‖A i j‖₊) :=
      Matrix.linfty_opNorm_def A
    rw [hnorm_eq, ← NNReal.coe_one, NNReal.coe_lt_coe]
    rw [Finset.sup_lt_iff (by simp : (⊥ : NNReal) < 1)]
    intro i _
    rw [← NNReal.coe_lt_coe, NNReal.coe_sum, NNReal.coe_one]
    simp_rw [coe_nnnorm, show ∀ j, ‖A i j‖ = A i j from fun j => Real.norm_of_nonneg (hA0 i j)]
    exact hrow i
  have hsum_mat : HasSum (fun n : ℕ => A ^ n) (∑' n : ℕ, A ^ n) :=
    (summable_geometric_of_norm_lt_one hnorm).hasSum
  have hinv : (1 - A)⁻¹ = ∑' n : ℕ, A ^ n :=
    Matrix.inv_eq_left_inv (geom_series_mul_neg A hnorm)
  have hbound : ∀ (M : Matrix ι ι ℝ) (i j : ι), ‖M i j‖ ≤ 1 * ‖M‖ := by
    intro M i j
    rw [one_mul]
    have hnorm_eq : ‖M‖ = ↑((Finset.univ : Finset ι).sup fun i => ∑ j, ‖M i j‖₊) :=
      Matrix.linfty_opNorm_def M
    rw [hnorm_eq, ← coe_nnnorm]
    norm_cast
    calc ‖M i j‖₊ ≤ ∑ j', ‖M i j'‖₊ :=
            Finset.single_le_sum (f := fun j' => ‖M i j'‖₊) (fun j' _ => zero_le)
              (Finset.mem_univ j)
      _ ≤ (Finset.univ : Finset ι).sup fun i => ∑ j, ‖M i j‖₊ :=
            Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have hpow : ∀ (n : ℕ) (i j : ι), 0 ≤ (A ^ n) i j := by
    intro n
    induction n with
    | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ n ih =>
        intro i j
        rw [pow_succ', Matrix.mul_apply]
        exact Finset.sum_nonneg fun k _ => mul_nonneg (hA0 i k) (ih k j)
  have hentry : HasSum (fun n : ℕ => (A ^ n) i j) ((1 - A)⁻¹ i j) := by
    rw [hinv]
    let hφ := LinearMap.mkContinuous
      ({ toFun := fun M : Matrix ι ι ℝ => M i j
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : (Matrix ι ι ℝ) →ₗ[ℝ] ℝ)
      1 (fun M => hbound M i j)
    exact hφ.hasSum hsum_mat
  rw [← hentry.tsum_eq]
  exact tsum_nonneg (fun n => hpow n i j)

end MathlibExt.Economics.InputOutput
