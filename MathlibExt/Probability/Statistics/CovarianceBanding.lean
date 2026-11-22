/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.SchurTest
public import Mathlib.Data.Int.Interval

/-!
# Banding a covariance matrix

Bickel and Levina's banding operator (P. J. Bickel and E. Levina, "Regularized estimation of
large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, Section 2.1) keeps the entries of
a `p × p` matrix within distance `k` of the diagonal and sets the others to zero:
`B_k(M) = [m_ij 1(|i - j| ≤ k)]`. Their Theorem 1 (operator-norm rate of the banded sample
covariance) rests on two deterministic operator-norm bounds, proved here from Schur's test
(`MathlibExt.Analysis.FunctionalAnalysis.SchurTest`), which is their inequality (A2)
`‖M‖ ≤ (‖M‖_{(1,1)} ‖M‖_{(∞,∞)})^{1/2}`:

* `norm_band_sub_le` (bias): for symmetric `M`, `‖B_k(M) - M‖ ≤ max_j ∑_{i : |i-j| > k} |m_ij|`,
  which is at most `C k^{-α}` on their class `U(ε₀, α, C)` (their (A6));
* `norm_band_le` (variance): if all entries of `A` are at most `t` in absolute value, then
  `‖B_k(A)‖ ≤ (2k + 1) t`; applied to `A = Σ̂ - Σ` it turns an entrywise bound into an
  operator-norm bound, as in their proof of Theorem 1.

The norm is the `ℓ²` operator norm (`Matrix.Norms.L2Operator`).
-/

@[expose] public section

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace MathlibExt.Probability.Statistics.CovarianceBanding

variable {p : ℕ}

/-- **Banding operator** (P. J. Bickel and E. Levina, *Ann. Statist.* 36 (2008), Section 2.1):
`B_k(M)_{ij} = m_ij` if `|i - j| ≤ k` and `0` otherwise. For `k ≥ p - 1` it is the identity. -/
def band (k : ℕ) (M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => if ((i : ℤ) - j).natAbs ≤ k then M i j else 0

theorem band_apply (k : ℕ) (M : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    band k M i j = if ((i : ℤ) - j).natAbs ≤ k then M i j else 0 := rfl

/-- **Banding is linear.** `B_k(A) - B_k(B) = B_k(A - B)`: banding acts entrywise. -/
theorem band_sub (k : ℕ) (A B : Matrix (Fin p) (Fin p) ℝ) :
    band k A - band k B = band k (A - B) := by
  ext i j
  simp only [Matrix.sub_apply, band_apply]
  split_ifs <;> simp

private theorem natAbs_sub_comm (i j : Fin p) :
    ((i : ℤ) - j).natAbs = ((j : ℤ) - i).natAbs := by
  rw [← Int.natAbs_neg, neg_sub]

/-- **Bias of banding** (P. J. Bickel and E. Levina, *Ann. Statist.* 36 (2008), inequality (A2)
applied to `B_k(M) - M`, giving (A6) on the class `U(ε₀, α, C)` of their equation (5)). For a
symmetric matrix `M` whose off-band column sums satisfy
`∑_{i : |i - j| > k} |m_ij| ≤ R` for every `j`, the operator norm of `B_k(M) - M` is at most
`R`. -/
theorem norm_band_sub_le (k : ℕ) {M : Matrix (Fin p) (Fin p) ℝ} (hM : M.IsSymm) {R : ℝ}
    (hR0 : 0 ≤ R)
    (hR : ∀ j : Fin p,
      ∑ i ∈ univ.filter (fun i : Fin p => k < ((i : ℤ) - j).natAbs), |M i j| ≤ R) :
    ‖band k M - M‖ ≤ R := by
  have hcol : ∀ j, ∑ i, ‖(band k M - M) i j‖ ≤ R := by
    intro j
    refine le_trans (le_of_eq ?_) (hR j)
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    simp only [Matrix.sub_apply, band_apply, Real.norm_eq_abs]
    split_ifs <;> first | omega | simp
  have hrow : ∀ i, ∑ j, ‖(band k M - M) i j‖ ≤ R := by
    intro i
    refine le_trans (le_of_eq ?_) (hR i)
    rw [sum_filter]
    refine sum_congr rfl fun j _ => ?_
    have hs : M i j = M j i := by
      rw [← Matrix.transpose_apply M j i, hM.eq]
    simp only [Matrix.sub_apply, band_apply, Real.norm_eq_abs, natAbs_sub_comm i j, hs]
    split_ifs <;> first | omega | simp
  calc ‖band k M - M‖ ≤ Real.sqrt (R * R) :=
        MathlibExt.Analysis.FunctionalAnalysis.SchurTest.norm_matrix_l2_le _ hR0 hR0 hrow hcol
    _ = R := Real.sqrt_mul_self hR0

private theorem card_band_le (k : ℕ) (i : Fin p) :
    (univ.filter fun j : Fin p => ((i : ℤ) - j).natAbs ≤ k).card ≤ 2 * k + 1 := by
  have h : (univ.filter fun j : Fin p => ((i : ℤ) - j).natAbs ≤ k).card ≤
      (Finset.Icc ((i : ℤ) - k) ((i : ℤ) + k)).card := by
    refine Finset.card_le_card_of_injOn (fun j => (j : ℤ)) (fun j hj => ?_) ?_
    · simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hj
      simp only [coe_Icc, Set.mem_Icc]
      omega
    · intro a _ b _ hab
      have hab' : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := hab
      exact Fin.ext (by exact_mod_cast hab')
  refine h.trans (le_of_eq ?_)
  rw [Int.card_Icc]
  omega

/-- **Operator norm of a banded matrix** (P. J. Bickel and E. Levina, *Ann. Statist.* 36 (2008),
proof of Theorem 1: `‖B_k(M)‖ ≤ (2k + 1) max_{ij} |m_ij|` via (A2)). If every entry of `A`
satisfies `|a_ij| ≤ t`, then `‖B_k(A)‖ ≤ (2k + 1) t`: each row and each column of `B_k(A)` has
at most `2k + 1` nonzero entries. -/
theorem norm_band_le (k : ℕ) {A : Matrix (Fin p) (Fin p) ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ i j, |A i j| ≤ t) : ‖band k A‖ ≤ (2 * k + 1) * t := by
  have hR0 : 0 ≤ (2 * k + 1 : ℝ) * t := by positivity
  have hsum : ∀ i, ∑ j, ‖band k A i j‖ ≤ (2 * k + 1) * t := by
    intro i
    calc ∑ j, ‖band k A i j‖
        = ∑ j ∈ univ.filter (fun j : Fin p => ((i : ℤ) - j).natAbs ≤ k), |A i j| := by
          rw [sum_filter]
          refine sum_congr rfl fun j _ => ?_
          simp only [band_apply, Real.norm_eq_abs]
          split_ifs <;> simp
      _ ≤ ∑ j ∈ univ.filter (fun j : Fin p => ((i : ℤ) - j).natAbs ≤ k), t :=
          sum_le_sum fun j _ => hA i j
      _ = (univ.filter (fun j : Fin p => ((i : ℤ) - j).natAbs ≤ k)).card * t := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * k + 1) * t := by
          gcongr
          exact_mod_cast card_band_le k i
  have hcol : ∀ j, ∑ i, ‖band k A i j‖ ≤ (2 * k + 1) * t := by
    intro j
    calc ∑ i, ‖band k A i j‖
        = ∑ i ∈ univ.filter (fun i : Fin p => ((j : ℤ) - i).natAbs ≤ k), |A i j| := by
          rw [sum_filter]
          refine sum_congr rfl fun i _ => ?_
          simp only [band_apply, Real.norm_eq_abs, natAbs_sub_comm i j]
          split_ifs <;> simp
      _ ≤ ∑ i ∈ univ.filter (fun i : Fin p => ((j : ℤ) - i).natAbs ≤ k), t :=
          sum_le_sum fun i _ => hA i j
      _ = (univ.filter (fun i : Fin p => ((j : ℤ) - i).natAbs ≤ k)).card * t := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * k + 1) * t := by
          gcongr
          exact_mod_cast card_band_le k j
  calc ‖band k A‖ ≤ Real.sqrt (((2 * k + 1) * t) * ((2 * k + 1) * t)) :=
        MathlibExt.Analysis.FunctionalAnalysis.SchurTest.norm_matrix_l2_le _ hR0 hR0 hsum hcol
    _ = (2 * k + 1) * t := Real.sqrt_mul_self hR0

/-- **The bandable class `U(ε₀, α, C)`** (P. J. Bickel and E. Levina, *Ann. Statist.* 36 (2008),
equation (5)): symmetric `p × p` matrices whose eigenvalues lie in `[ε₀, 1/ε₀]` (stated through
the quadratic form) and whose off-band column sums decay polynomially,
`max_j ∑_{i : |i - j| > k} |σ_ij| ≤ C k^{-α}` for every band width `k ≥ 1`. -/
def bandableClass (ε₀ α C : ℝ) : Set (Matrix (Fin p) (Fin p) ℝ) :=
  {M | M.IsSymm ∧
    (∀ x : Fin p → ℝ, ε₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ M *ᵥ x ∧ x ⬝ᵥ M *ᵥ x ≤ ε₀⁻¹ * (x ⬝ᵥ x)) ∧
    ∀ k : ℕ, 0 < k → ∀ j : Fin p,
      ∑ i ∈ univ.filter (fun i : Fin p => k < ((i : ℤ) - j).natAbs), |M i j| ≤ C * (k : ℝ) ^ (-α)}

/-- **Uniform bias bound on the bandable class** (P. J. Bickel and E. Levina, *Ann. Statist.*
36 (2008), (A6) in the proof of Theorem 1). For `M ∈ U(ε₀, α, C)` with `C ≥ 0` and every band
width `k ≥ 1`, `‖B_k(M) - M‖ ≤ C k^{-α}`. -/
theorem norm_band_sub_le_of_mem_bandableClass {ε₀ α C : ℝ} (hC : 0 ≤ C)
    {M : Matrix (Fin p) (Fin p) ℝ} (hM : M ∈ bandableClass ε₀ α C) {k : ℕ} (hk : 0 < k) :
    ‖band k M - M‖ ≤ C * (k : ℝ) ^ (-α) :=
  norm_band_sub_le k hM.1 (by positivity) (hM.2.2 k hk)

end MathlibExt.Probability.Statistics.CovarianceBanding
