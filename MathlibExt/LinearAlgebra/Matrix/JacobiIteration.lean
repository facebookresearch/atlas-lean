/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Convergence of the Jacobi iteration

For a square system `A x = b`, one Jacobi sweep maps `x` to the vector `J x` whose `i`-th entry is
`(b i - ∑_{j ≠ i} A i j * x j) / A i i`. If `A` is strictly diagonally dominant by rows,
`∑_{j ≠ i} |A i j| < |A i i|` for every `i`, then `J` is a contraction for the sup norm, with
constant `q = max_i (∑_{j ≠ i} |A i j|) / |A i i| < 1`. Its fixed point solves `A x = b`, and the
Jacobi iterates converge to it from any starting point.

## Main results

* `jacobi_iteration_converges`: the Jacobi iterates of a strictly diagonally dominant system
  converge, from every starting point, to a solution of `A x = b`.

## References

* Mathlib, `docs/undergrad.yaml`, "Numerical Analysis" / "Iterative methods" / "Jacobian".
* G. H. Golub and C. F. Van Loan, *Matrix Computations*, 4th ed., §11.2.
-/

@[expose] public section

open scoped BigOperators Topology NNReal

namespace MathlibExt.LinearAlgebra.Matrix.JacobiIterationWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One Jacobi sweep is a contraction for the sup norm when `A` is strictly diagonally dominant
by rows. -/
private lemma jacobi_contractingWith (A : Matrix n n ℝ) (b : n → ℝ)
    (hA : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) :
    ∃ q : ℝ≥0, ContractingWith q
      (fun x : n → ℝ => fun i => (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i) := by
  -- The row ratios `r i = (∑_{j ≠ i} |A i j|) / |A i i|` lie in `[0, 1)`.
  have hpos : ∀ i, 0 < |A i i| := fun i ↦
    (Finset.sum_nonneg fun j _ ↦ abs_nonneg (A i j)).trans_lt (hA i)
  let r : n → ℝ≥0 := fun i ↦
    ⟨(∑ j ∈ Finset.univ.erase i, |A i j|) / |A i i|,
      div_nonneg (Finset.sum_nonneg fun j _ ↦ abs_nonneg _) (abs_nonneg _)⟩
  have hr : ∀ i, r i < 1 := fun i ↦ by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    exact (div_lt_one (hpos i)).2 (hA i)
  refine ⟨Finset.univ.sup r, (Finset.sup_lt_iff zero_lt_one).2 fun i _ ↦ hr i,
    LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  have hsub : (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i -
      (b i - ∑ j ∈ Finset.univ.erase i, A i j * y j) / A i i =
      (∑ j ∈ Finset.univ.erase i, A i j * (y j - x j)) / A i i := by
    rw [← sub_div]
    congr 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hsum : |∑ j ∈ Finset.univ.erase i, A i j * (y j - x j)| ≤
      (∑ j ∈ Finset.univ.erase i, |A i j|) * ‖x - y‖ := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← Real.norm_eq_abs, norm_sub_rev]
    exact norm_le_pi_norm (x - y) j
  have hri : (r i : ℝ) ≤ (Finset.univ.sup r : ℝ≥0) :=
    NNReal.coe_le_coe.2 (Finset.le_sup (Finset.mem_univ i))
  calc ‖((fun i => (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i) -
        (fun i => (b i - ∑ j ∈ Finset.univ.erase i, A i j * y j) / A i i)) i‖
      = |∑ j ∈ Finset.univ.erase i, A i j * (y j - x j)| / |A i i| := by
        rw [Pi.sub_apply, hsub, Real.norm_eq_abs, abs_div]
    _ ≤ (∑ j ∈ Finset.univ.erase i, |A i j|) * ‖x - y‖ / |A i i| :=
        div_le_div_of_nonneg_right hsum (abs_nonneg _)
    _ = (r i : ℝ) * ‖x - y‖ := by
        rw [show (r i : ℝ) = (∑ j ∈ Finset.univ.erase i, |A i j|) / |A i i| from rfl]
        ring
    _ ≤ (Finset.univ.sup r : ℝ≥0) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hri (norm_nonneg _)

/--
**Convergence of the Jacobi method for strictly diagonally dominant matrices.** Let $A$ be a
real square matrix with rows and columns indexed by a finite type, and let $b$ be a real vector.
Suppose $A$ is strictly diagonally dominant: $\sum_{j \ne i} |A_{ij}| < |A_{ii}|$ for every $i$.
Define the Jacobi sweep $J$ by $J(x)_i = \bigl(b_i - \sum_{j \ne i} A_{ij} x_j\bigr) / A_{ii}$.
Then there is a vector $x^*$ with $A x^* = b$ such that, for every starting vector $x_0$, the
iterates $J^k(x_0)$ converge to $x^*$ as $k \to \infty$.

Sources: Mathlib repository, `docs/undergrad.yaml` (the undergraduate curriculum list),
section "Numerical Analysis" / "Iterative methods" / "Jacobian";
G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins Univ. Press,
2013, §11.2; https://en.wikipedia.org/wiki/Jacobi_method

Proves `Wanted` entry `jacobi_iteration_converges`.
-/
theorem jacobi_iteration_converges
    (A : Matrix n n ℝ) (b : n → ℝ)
    (hA : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) :
    ∃ xStar : n → ℝ, A.mulVec xStar = b ∧ ∀ x₀ : n → ℝ,
      Filter.Tendsto
        (fun k =>
          (fun x : n → ℝ => fun i => (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i)^[k]
            x₀)
        Filter.atTop (𝓝 xStar) := by
  obtain ⟨q, hJ⟩ := jacobi_contractingWith A b hA
  refine ⟨ContractingWith.fixedPoint _ hJ, ?_, hJ.tendsto_iterate_fixedPoint⟩
  -- The fixed point solves the system, row by row.
  have hfix := hJ.fixedPoint_isFixedPt
  set x := ContractingWith.fixedPoint _ hJ
  ext i
  have hAii : A i i ≠ 0 := abs_pos.1
    ((Finset.sum_nonneg fun j _ ↦ abs_nonneg (A i j)).trans_lt (hA i))
  have hi : (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i = x i := congr_fun hfix i
  rw [div_eq_iff hAii] at hi
  rw [Matrix.mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  linarith

end MathlibExt.LinearAlgebra.Matrix.JacobiIterationWanted
