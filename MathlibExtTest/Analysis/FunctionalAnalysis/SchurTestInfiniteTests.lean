/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.SchurTestInfinite
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.SchurTestInfiniteTests

open MathlibExt.Analysis.FunctionalAnalysis.SchurTestInfinite
open scoped _root_.lp InnerProductSpace InnerProduct

/-- The zero matrix satisfies Schur's test with `R = C = 0`, and its
operator is zero. -/
example : schurInfOperator (0 : ℕ → ℕ → ℝ) (R := 0) (C := 0)
    (by intro i; simp) (by intro i; simp)
    (by intro j; simp) (by intro j; simp) = 0 := by
  ext x i
  simp [schurInfOperator_apply]

/-- Row summability for the identity matrix. -/
private theorem diagOne_row_summable (i : ℕ) :
    Summable fun j => ‖(if i = j then (1 : ℝ) else 0)‖ := by
  apply summable_of_ne_finset_zero (s := {i})
  intro j hj
  simp only [Finset.mem_singleton] at hj
  rw [ite_eq_right (Ne.symm hj), norm_zero]

/-- Row sums of the identity matrix equal `1`. -/
private theorem diagOne_row_sum (i : ℕ) :
    ∑' j, ‖(if i = j then (1 : ℝ) else 0)‖ = 1 := by
  rw [tsum_eq_single i (fun j hj => by rw [ite_eq_right (Ne.symm hj), norm_zero])]
  simp

/-- Column summability for the identity matrix. -/
private theorem diagOne_col_summable (j : ℕ) :
    Summable fun i => ‖(if i = j then (1 : ℝ) else 0)‖ := by
  apply summable_of_ne_finset_zero (s := {j})
  intro i hi
  simp only [Finset.mem_singleton] at hi
  rw [ite_eq_right hi, norm_zero]

/-- Column sums of the identity matrix equal `1`. -/
private theorem diagOne_col_sum (j : ℕ) :
    ∑' i, ‖(if i = j then (1 : ℝ) else 0)‖ = 1 := by
  rw [tsum_eq_single j (fun i hi => by rw [ite_eq_right hi, norm_zero])]
  simp

/-- The Schur operator of the identity matrix is the identity. -/
example : schurInfOperator (fun i j : ℕ => if i = j then (1 : ℝ) else 0)
    diagOne_row_summable (fun i => le_of_eq (diagOne_row_sum i))
    diagOne_col_summable (fun j => le_of_eq (diagOne_col_sum j)) = 1 := by
  ext x i
  rw [schurInfOperator_apply]
  rw [tsum_eq_single i (fun j hj => by rw [ite_eq_right (Ne.symm hj), zero_mul])]
  simp

/-- The Schur operator of the identity matrix has norm at most `1`. -/
example : ‖schurInfOperator (fun i j : ℕ => if i = j then (1 : ℝ) else 0)
    diagOne_row_summable (fun i => le_of_eq (diagOne_row_sum i))
    diagOne_col_summable (fun j => le_of_eq (diagOne_col_sum j))‖ ≤ 1 :=
  norm_schurInfOperator_le_of_le _ (by norm_num) diagOne_row_summable
    (fun i => le_of_eq (diagOne_row_sum i)) diagOne_col_summable
    (fun j => le_of_eq (diagOne_col_sum j))

/-- The identity matrix is not Hilbert–Schmidt: its squared entries are not
summable, since the diagonal entries are all `1`. This separates Schur's test
from batch 68, where Hilbert–Schmidt matrices are the ones with summable
squared entries. -/
example : ¬ Summable fun p : ℕ × ℕ =>
    ‖(fun i j : ℕ => if i = j then (1 : ℝ) else 0) p.1 p.2‖ ^ 2 := by
  intro h
  have hinner : ∀ i : ℕ, Summable fun j : ℕ =>
      ‖(if i = j then (1 : ℝ) else 0)‖ ^ 2 := by
    intro i
    apply summable_of_ne_finset_zero (s := {i})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [ite_eq_right (Ne.symm hj)]
  have hrow2 : ∀ i : ℕ, ∑' j : ℕ, ‖(if i = j then (1 : ℝ) else 0)‖ ^ 2 = 1 := by
    intro i
    rw [tsum_eq_single i (fun j hj => by simp [ite_eq_right (Ne.symm hj)])]
    simp
  have hconst : Summable fun _ : ℕ => (1 : ℝ) :=
    (h.prod).congr (fun i => hrow2 i)
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp hconst)

/-- Row summability for the geometric diagonal matrix. -/
private theorem diagGeom_row_summable (i : ℕ) :
    Summable fun j => ‖(if i = j then (1 / 2 : ℝ) ^ i else 0)‖ := by
  apply summable_of_ne_finset_zero (s := {i})
  intro j hj
  simp only [Finset.mem_singleton] at hj
  rw [ite_eq_right (Ne.symm hj), norm_zero]

/-- Row sums of the geometric diagonal matrix: `(1/2)^i ≤ 1`. -/
private theorem diagGeom_row_sum_le (i : ℕ) :
    ∑' j, ‖(if i = j then (1 / 2 : ℝ) ^ i else 0)‖ ≤ 1 := by
  rw [tsum_eq_single i (fun j hj => by rw [ite_eq_right (Ne.symm hj), norm_zero]),
    ite_eq_left rfl, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ i)]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Column summability for the geometric diagonal matrix. -/
private theorem diagGeom_col_summable (j : ℕ) :
    Summable fun i => ‖(if i = j then (1 / 2 : ℝ) ^ i else 0)‖ := by
  apply summable_of_ne_finset_zero (s := {j})
  intro i hi
  simp only [Finset.mem_singleton] at hi
  rw [ite_eq_right hi, norm_zero]

/-- Column sums of the geometric diagonal matrix: `(1/2)^j ≤ 1`. -/
private theorem diagGeom_col_sum_le (j : ℕ) :
    ∑' i, ‖(if i = j then (1 / 2 : ℝ) ^ i else 0)‖ ≤ 1 := by
  rw [tsum_eq_single j (fun i hi => by rw [ite_eq_right hi, norm_zero]),
    ite_eq_left rfl, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ j)]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The Schur operator of the geometric diagonal matrix is diagonal with
entries `(1/2)^i`. -/
example (x : ℓ²(ℕ, ℝ)) (i : ℕ) :
    schurInfOperator (fun i j : ℕ => if i = j then (1 / 2 : ℝ) ^ i else 0)
      diagGeom_row_summable diagGeom_row_sum_le
      diagGeom_col_summable diagGeom_col_sum_le x i = (1 / 2 : ℝ) ^ i * x i := by
  rw [schurInfOperator_apply]
  rw [tsum_eq_single i (fun j hj => by rw [ite_eq_right (Ne.symm hj), zero_mul])]
  simp

/-- The Schur operator of the geometric diagonal matrix has norm at most `1`. -/
example : ‖schurInfOperator (fun i j : ℕ => if i = j then (1 / 2 : ℝ) ^ i else 0)
    diagGeom_row_summable diagGeom_row_sum_le
    diagGeom_col_summable diagGeom_col_sum_le‖ ≤ 1 :=
  norm_schurInfOperator_le_of_le _ (by norm_num) diagGeom_row_summable
    diagGeom_row_sum_le diagGeom_col_summable diagGeom_col_sum_le

/-- Row summability for the dyadic matrix `(1/2)^(i+j)`. -/
private theorem dyadic_row_summable (i : ℕ) :
    Summable fun j => ‖(1 / 2 : ℝ) ^ (i + j)‖ := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)).mul_left ((1 / 2 : ℝ) ^ i)
  refine h.congr (fun j => ?_)
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (i + j)), pow_add]

/-- Row sums of the dyadic matrix: `(1/2)^i * 2 ≤ 2`. -/
private theorem dyadic_row_sum_le (i : ℕ) :
    ∑' j, ‖(1 / 2 : ℝ) ^ (i + j)‖ ≤ 2 := by
  have hsum : ∑' j, ‖(1 / 2 : ℝ) ^ (i + j)‖ = (1 / 2 : ℝ) ^ i * 2 := by
    calc ∑' j, ‖(1 / 2 : ℝ) ^ (i + j)‖
        = ∑' j, (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ j :=
          tsum_congr fun j => by
            rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (i + j)),
              pow_add]
      _ = (1 / 2 : ℝ) ^ i * 2 := by rw [tsum_mul_left, tsum_geometric_two]
  rw [hsum]
  calc (1 / 2 : ℝ) ^ i * 2 ≤ 1 * 2 :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
    _ = 2 := one_mul _

/-- Column summability for the dyadic matrix. -/
private theorem dyadic_col_summable (j : ℕ) :
    Summable fun i => ‖(1 / 2 : ℝ) ^ (i + j)‖ := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)).mul_left ((1 / 2 : ℝ) ^ j)
  refine h.congr (fun i => ?_)
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (i + j)), add_comm i j,
    pow_add]

/-- Column sums of the dyadic matrix: `(1/2)^j * 2 ≤ 2`. -/
private theorem dyadic_col_sum_le (j : ℕ) :
    ∑' i, ‖(1 / 2 : ℝ) ^ (i + j)‖ ≤ 2 := by
  have hsum : ∑' i, ‖(1 / 2 : ℝ) ^ (i + j)‖ = (1 / 2 : ℝ) ^ j * 2 := by
    calc ∑' i, ‖(1 / 2 : ℝ) ^ (i + j)‖
        = ∑' i, (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ i :=
          tsum_congr fun i => by
            rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (i + j)),
              add_comm i j, pow_add]
      _ = (1 / 2 : ℝ) ^ j * 2 := by rw [tsum_mul_left, tsum_geometric_two]
  rw [hsum]
  calc (1 / 2 : ℝ) ^ j * 2 ≤ 1 * 2 :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
    _ = 2 := one_mul _

/-- The dyadic operator sends `e₀` to the geometric sequence `(1/2)^i`. -/
example (i : ℕ) :
    schurInfOperator (fun i j : ℕ => (1 / 2 : ℝ) ^ (i + j))
      dyadic_row_summable dyadic_row_sum_le
      dyadic_col_summable dyadic_col_sum_le (lp.single 2 0 (1 : ℝ)) i =
        (1 / 2 : ℝ) ^ i := by
  show ∑' j, (1 / 2 : ℝ) ^ (i + j) *
      ((lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)) j) = (1 / 2 : ℝ) ^ i
  rw [tsum_eq_single 0 (fun j hj => by
    rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) hj, mul_zero])]
  simp

/-- The dyadic operator has norm at most `2`. -/
example : ‖schurInfOperator (fun i j : ℕ => (1 / 2 : ℝ) ^ (i + j))
    dyadic_row_summable dyadic_row_sum_le
    dyadic_col_summable dyadic_col_sum_le‖ ≤ 2 :=
  norm_schurInfOperator_le_of_le _ (by norm_num) dyadic_row_summable
    dyadic_row_sum_le dyadic_col_summable dyadic_col_sum_le

/-- The dyadic operator is self-adjoint: its matrix is real and symmetric,
so its conjugate transpose is itself. -/
example : (schurInfOperator (fun i j : ℕ => (1 / 2 : ℝ) ^ (i + j))
    dyadic_row_summable dyadic_row_sum_le
    dyadic_col_summable dyadic_col_sum_le)† =
    schurInfOperator (fun i j : ℕ => (1 / 2 : ℝ) ^ (i + j))
    dyadic_row_summable dyadic_row_sum_le
    dyadic_col_summable dyadic_col_sum_le := by
  rw [adjoint_schurInfOperator]
  apply schurInfOperator_congr
  funext i j
  rw [star_trivial, add_comm j i]

#print axioms norm_schurInfOperator_le
#print axioms schurInfOperator_apply
#print axioms norm_schurInfOperator_le_of_le
#print axioms adjoint_schurInfOperator

end MathlibExt.Analysis.FunctionalAnalysis.SchurTestInfiniteTests
