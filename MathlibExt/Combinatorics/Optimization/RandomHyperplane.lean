/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Optimization.MaxCutRelaxation
public import MathlibExt.Probability.Distributions.StdGaussianHyperplane

/-!
# Random-hyperplane rounding for MAX CUT

M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and
satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145.

Their algorithm puts `i` in `S` when `v_i · r ≥ 0` for a random direction `r`; they draw `r`
uniformly on the sphere and note (p. 1121) that a standard Gaussian vector gives the same cut.
Here `r` is standard Gaussian.

* `measureReal_sign_ne`: their Lemma 3.2, `P[sgn(u · r) ≠ sgn(v · r)] = arccos(u · v) / π`;
* `integral_cutWeight_hyperplane`: their Theorem 3.1, the expected cut weight;
* `gwConstant_mul_vectorObjective_le_integral`: their Theorem 3.3;
* `gwConstant_mul_cutWeight_le_integral`: with optimal vectors, the expected cut is at least `α`
  times every cut; `gwConstant_mul_cutWeight_sub_le_integral` is the version for vectors within
  `ε` of optimal, as in the paper.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Optimization.GoemansWilliamson

open Real MeasureTheory ProbabilityTheory Set
  MathlibExt.Probability.Distributions.StdGaussianHyperplane

/-- **Goemans–Williamson Lemma 3.2: probability that a random hyperplane separates two unit
vectors.** For unit vectors `u`, `v ∈ ℝ^n` and a standard Gaussian vector `r`,
`P[sgn(u · r) ≠ sgn(v · r)] = arccos(u · v) / π`, with `sgn x = 1` for `x ≥ 0` (Goemans and
Williamson, *J. ACM* 42(6) (1995), Lemma 3.2, stated there for `r` uniform on the sphere; the
Gaussian form follows from their remark on p. 1121). -/
theorem measureReal_sign_ne {n : ℕ} {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {r | (0 ≤ inner ℝ u r) ≠ (0 ≤ inner ℝ v r)} = arccos (inner ℝ u v) / π := by
  rw [measureReal_def, stdGaussian_sign_ne hu hv,
    ENNReal.toReal_ofReal (div_nonneg (arccos_nonneg _) pi_pos.le)]


/-- **Goemans–Williamson Theorem 3.1: expected weight of the random-hyperplane cut.** For
weights `w_ij`, unit vectors `v_i ∈ ℝ^n` and a standard Gaussian vector `r`, the cut
`S = {i : v_i · r ≥ 0}` has expected weight `∑_{i<j} w_ij arccos(v_i · v_j) / π` (Goemans and
Williamson, *J. ACM* 42(6) (1995), Theorem 3.1, from Lemma 3.2 by linearity of expectation). -/
theorem integral_cutWeight_hyperplane {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (w : ι → ι → ℝ) {v : ι → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, ‖v i‖ = 1) :
    ∫ r, cutWeight w (Finset.univ.filter fun i => 0 ≤ inner ℝ (v i) r)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = hyperplaneExpectation w v := by
  set A : ι × ι → Set (EuclideanSpace ℝ (Fin n)) :=
    fun p => {r | (0 ≤ inner ℝ (v p.1) r) ≠ (0 ≤ inner ℝ (v p.2) r)} with hAdef
  have hA : ∀ p, MeasurableSet (A p) := fun p =>
    measurableSet_sign_ne (continuous_const.inner continuous_id)
      (continuous_const.inner continuous_id)
  have hfun : (fun r => cutWeight w (Finset.univ.filter fun i => 0 ≤ inner ℝ (v i) r)) =
      fun r => ∑ p ∈ pairs ι, (A p).indicator (fun _ => w p.1 p.2) r := by
    funext r
    unfold cutWeight
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hAdef, indicator, mem_ofPred_eq,
      ne_eq, eq_iff_iff]
    split_ifs <;> tauto
  rw [hfun, integral_finsetSum _ fun p _ => (integrable_const _).indicator (hA p)]
  unfold hyperplaneExpectation
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_indicator_const _ (hA p), smul_eq_mul, hAdef]
  simp only
  rw [measureReal_sign_ne (hv p.1) (hv p.2), mul_comm]

/-- **Goemans–Williamson Theorem 3.3.** For nonnegative weights and unit vectors `v_i ∈ ℝ^n`,
the random-hyperplane cut has expected weight at least
`α · ∑_{i<j} w_ij (1 - v_i · v_j) / 2` (Goemans and Williamson, *J. ACM* 42(6) (1995),
Theorem 3.3). -/
theorem gwConstant_mul_vectorObjective_le_integral {ι : Type*} [Fintype ι] [LinearOrder ι]
    {n : ℕ} {w : ι → ι → ℝ} (hw : ∀ i j, 0 ≤ w i j) {v : ι → EuclideanSpace ℝ (Fin n)}
    (hv : ∀ i, ‖v i‖ = 1) :
    gwConstant * vectorObjective w v ≤
      ∫ r, cutWeight w (Finset.univ.filter fun i => 0 ≤ inner ℝ (v i) r)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [integral_cutWeight_hyperplane w hv]
  exact gwConstant_mul_vectorObjective_le hw hv

/-- **The Goemans–Williamson guarantee.** For nonnegative weights, if unit vectors `v_i ∈ ℝ^n`
attain the relaxation value `Z_P`, the random-hyperplane cut has expected weight at least
`α · w(S, S̄)` for every vertex set `S`
(Goemans and Williamson, *J. ACM* 42(6) (1995), §2 and Theorem 3.3; they also handle vectors
within `ε` of optimal, which is what a semidefinite-programming solver returns). With
`α > 0.87856` (Lemma 3.5) this is their `0.87856` guarantee in expectation. -/
theorem gwConstant_mul_cutWeight_le_integral {ι : Type*} [Fintype ι] [LinearOrder ι]
    {n : ℕ} (hn : 0 < n) {w : ι → ι → ℝ} (hw : ∀ i j, 0 ≤ w i j)
    {v : ι → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, ‖v i‖ = 1)
    (hopt : vectorObjective w v = relaxationValue w n) (S : Finset ι) :
    gwConstant * cutWeight w S ≤
      ∫ r, cutWeight w (Finset.univ.filter fun i => 0 ≤ inner ℝ (v i) r)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hα : 0 ≤ gwConstant := le_trans (by norm_num) (le_of_lt lt_gwConstant)
  calc gwConstant * cutWeight w S ≤ gwConstant * vectorObjective w v := by
        rw [hopt]; exact mul_le_mul_of_nonneg_left (cutWeight_le_relaxationValue hn w S) hα
    _ ≤ _ := gwConstant_mul_vectorObjective_le_integral hw hv

/-- **The Goemans–Williamson guarantee for nearly optimal vectors.** For nonnegative weights, if
unit vectors `v_i ∈ ℝ^n` have relaxation objective at least `Z_P - ε`, the random-hyperplane cut
has expected weight at least `α · (w(S, S̄) - ε)` for every vertex set `S` (Goemans and
Williamson, *J. ACM* 42(6) (1995), §2: vectors of value greater than `Z_P - ε`, as returned by a
semidefinite-programming algorithm, give a cut of expected weight at least `α (Z_P - ε)`). -/
theorem gwConstant_mul_cutWeight_sub_le_integral {ι : Type*} [Fintype ι] [LinearOrder ι]
    {n : ℕ} (hn : 0 < n) {w : ι → ι → ℝ} (hw : ∀ i j, 0 ≤ w i j)
    {v : ι → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, ‖v i‖ = 1) {ε : ℝ}
    (hε : relaxationValue w n - ε ≤ vectorObjective w v) (S : Finset ι) :
    gwConstant * (cutWeight w S - ε) ≤
      ∫ r, cutWeight w (Finset.univ.filter fun i => 0 ≤ inner ℝ (v i) r)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hα : 0 ≤ gwConstant := le_trans (by norm_num) (le_of_lt lt_gwConstant)
  have hcut := cutWeight_le_relaxationValue hn w S
  calc gwConstant * (cutWeight w S - ε) ≤ gwConstant * vectorObjective w v :=
        mul_le_mul_of_nonneg_left (by linarith) hα
    _ ≤ _ := gwConstant_mul_vectorObjective_le_integral hw hv

end MathlibExt.Combinatorics.Optimization.GoemansWilliamson
