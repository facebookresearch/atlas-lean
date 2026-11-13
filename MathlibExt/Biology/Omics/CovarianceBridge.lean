/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.PCA

/-!
# Centered sample covariance versus the uncentered second moment

Omics pipelines feed a samples × features matrix `X` (rows are samples, columns are features)
to PCA, clustering or matrix factorization. Some tools work with the column-centered sample
covariance `S = (n - 1)⁻¹ (X - 𝟙 x̄ᵀ)ᵀ (X - 𝟙 x̄ᵀ)`, others with the uncentered second moment
`n⁻¹ Xᵀ X`. This file records the exact bridge between the two before any such composition, the
rank and singularity behaviour of `S`, and a confounded-batch design in which the batch effect
is not identifiable from `S`.

The sample covariance, the centered matrix and the column means are the canonical ones from
`MathlibExt.Probability.Statistics.PCA` (`sampleCov`, `center`, `colMean`); nothing about PCA
is redefined here.

## Main definitions

* `secondMoment X` : the uncentered second-moment matrix `n⁻¹ Xᵀ X`.
* `batchModel E μ b s β δ` : the additive design `X = E + 𝟙 μᵀ + b βᵀ + s δᵀ` with a batch
  covariate `b`, a biological covariate `s`, batch effect `β` and biological signal `δ`.

## Main results

* `transpose_center_mul_center` : the scatter identity
  `(X - 𝟙 x̄ᵀ)ᵀ (X - 𝟙 x̄ᵀ) = Xᵀ X - n x̄ x̄ᵀ`.
* `sub_one_smul_sampleCov`, `sampleCov_eq_secondMoment` : `(n - 1) S = Xᵀ X - n x̄ x̄ᵀ` for
  every `n`, and `S = n / (n - 1) • (n⁻¹ Xᵀ X - x̄ x̄ᵀ)` for `2 ≤ n` (Bessel's correction).
* `sampleCov_add_vecMulVec_one` : `S` does not see a common shift `𝟙 cᵀ` of all samples, while
  the second moment does.
* `center_eq_zero_of_le_one`, `sampleCov_eq_zero_of_le_one` : with at most one sample the
  centered matrix and `S` vanish, so the rank and null-direction results below need no lower
  bound on `n`.
* `rank_sampleCov`, `rank_center_le`, `det_sampleCov_eq_zero_of_le` : `rank S = rank (X - 𝟙 x̄ᵀ)
  ≤ n - 1`, so `S` is singular whenever there are no more samples than features.
* `sampleCov_mulVec_eq_zero_iff`, `det_sampleCov_eq_zero_iff` : `S w = 0` exactly when every
  sample has the same projection on `w`, so `S` is singular exactly when the samples lie in an
  affine hyperplane.
* `rank_center_le_rank`, `rank_le_rank_center_add_one` : centering lowers the rank of the data
  by at most one.
* `posDef_sampleCov_iff` : `S` is positive definite exactly when no affine hyperplane contains
  all samples.
* `sampleCov_batchModel_eq_of_add_eq`, `not_exists_batch_estimator` : when the batch and the
  biological condition are confounded (`s = b`), `S` depends on `(β, δ)` only through `β + δ`,
  so no function of `S` recovers the batch effect (`not_exists_signal_estimator`: nor the
  signal).
* `sampleCov_batchModel_confounded_noiseless`, `rank_sampleCov_vecMulVec_le`,
  `rank_sampleCov_batchModel_confounded_noiseless_le` : without noise, the confounded `S` is
  `var(b) • (β + δ)(β + δ)ᵀ`, of rank at most one.

## References

Source receipt (API-00 reuse search): `MathlibExt.Probability.Statistics.PCA`
supplies `colMean`, `center`, `sampleCov`, `sum_center` and `sampleVar_scores`; Mathlib supplies
`Matrix.rank_transpose_mul_self`, `Matrix.exists_mulVec_eq_zero_iff` and the `vecMulVec`
algebra. No existing statement of the scatter identity or of the rank bound for centered data
was found in pinned Mathlib or `MathlibExt` (base 53666a3c1). Related, landed on `main` after
that base: `MathlibExt.Biology.Omics.Pseudobulk.not_identifiable_of_confounded` proves that the
condition effect `τ` is not identifiable from the full data law of the scalar cell-level
hierarchical model (cells indexed by donor × cell, donor-level batch and condition covariates)
under perfect confounding. That is a statement about a probability law; the results here are
about the centered sample covariance as a matrix and do not duplicate it.

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  §3.3 (the sample covariance and the identity `∑ (xᵢ - x̄)(xᵢ - x̄)ᵀ = ∑ xᵢ xᵢᵀ - n x̄ x̄ᵀ`).
* J. T. Leek et al., "Tackling the widespread and critical impact of batch effects in
  high-throughput data", Nat. Rev. Genet. 11 (2010), 733–739 (confounded designs).
-/

@[expose] public section

namespace MathlibExt.Biology.Omics.CovarianceBridge

open Matrix
open MathlibExt.Probability.Statistics.PCA

variable {n p : ℕ}

/-! ### The uncentered second moment and the scatter identity -/

/-- The uncentered second-moment matrix `n⁻¹ Xᵀ X` of an `n × p` data matrix (rows are
samples): entry `(j, k)` is `n⁻¹ ∑ᵢ Xᵢⱼ Xᵢₖ`. For `n = 0` it is the zero matrix. -/
noncomputable def secondMoment (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (n : ℝ)⁻¹ • (Xᵀ * X)

/-- Column sums are `n` times the column means (for every `n`, including `n = 0`). -/
theorem sum_eq_mul_colMean (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    ∑ i, X i j = n * colMean X j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [colMean]
    field_simp

/-- The centered matrix is `X - 𝟙 x̄ᵀ`. -/
theorem center_eq_sub_vecMulVec (X : Matrix (Fin n) (Fin p) ℝ) :
    center X = X - vecMulVec (fun _ => 1) (colMean X) := by
  ext i j
  simp [center, vecMulVec_apply]

/-- **Scatter identity.** `(X - 𝟙 x̄ᵀ)ᵀ (X - 𝟙 x̄ᵀ) = Xᵀ X - n x̄ x̄ᵀ`. -/
theorem transpose_center_mul_center (X : Matrix (Fin n) (Fin p) ℝ) :
    (center X)ᵀ * center X = Xᵀ * X - (n : ℝ) • vecMulVec (colMean X) (colMean X) := by
  ext j k
  rw [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp only [mul_apply, transpose_apply, center, of_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sum_eq_mul_colMean,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Bridge, unnormalized.** `(n - 1) S = Xᵀ X - n x̄ x̄ᵀ` for every `n` (for `n = 1` both
sides vanish, since the single sample equals its mean). -/
theorem sub_one_smul_sampleCov (X : Matrix (Fin n) (Fin p) ℝ) :
    ((n : ℝ) - 1) • sampleCov X = Xᵀ * X - (n : ℝ) • vecMulVec (colMean X) (colMean X) := by
  rw [← transpose_center_mul_center, sampleCov, smul_smul]
  rcases eq_or_ne ((n : ℝ) - 1) 0 with h | h
  · have hn : n = 1 := by exact_mod_cast sub_eq_zero.mp h
    subst hn
    have hc : center X = 0 := by
      ext i j
      fin_cases i
      simp [center, colMean]
    simp [hc]
  · rw [mul_inv_cancel₀ h, one_smul]

/-- **Bridge.** `S = (n - 1)⁻¹ (Xᵀ X - n x̄ x̄ᵀ)` (for every `n`, with PCA's junk value
`(0 : ℝ)⁻¹ = 0` at `n = 1`). -/
theorem sampleCov_eq_sub (X : Matrix (Fin n) (Fin p) ℝ) :
    sampleCov X =
      ((n : ℝ) - 1)⁻¹ • (Xᵀ * X - (n : ℝ) • vecMulVec (colMean X) (colMean X)) := by
  rw [sampleCov, transpose_center_mul_center]

/-- **Second moment minus mean outer product.** For `0 < n`, the biased (maximum-likelihood)
covariance `n⁻¹ (X - 𝟙 x̄ᵀ)ᵀ (X - 𝟙 x̄ᵀ)` is `n⁻¹ Xᵀ X - x̄ x̄ᵀ`. -/
theorem inv_smul_transpose_center_mul_center (X : Matrix (Fin n) (Fin p) ℝ) (hn : 0 < n) :
    (n : ℝ)⁻¹ • ((center X)ᵀ * center X) =
      secondMoment X - vecMulVec (colMean X) (colMean X) := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [transpose_center_mul_center, smul_sub, smul_smul, inv_mul_cancel₀ this, one_smul,
    secondMoment]

/-- **Bessel's correction.** For `2 ≤ n`, `S = n / (n - 1) • (n⁻¹ Xᵀ X - x̄ x̄ᵀ)`. -/
theorem sampleCov_eq_secondMoment (X : Matrix (Fin n) (Fin p) ℝ) (hn : 2 ≤ n) :
    sampleCov X =
      ((n : ℝ) / ((n : ℝ) - 1)) • (secondMoment X - vecMulVec (colMean X) (colMean X)) := by
  rw [← inv_smul_transpose_center_mul_center X (by omega), smul_smul, sampleCov]
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by positivity
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  congr 1
  field_simp

/-- For data with zero column means, `S = n / (n - 1) • n⁻¹ Xᵀ X`: centered and uncentered
matrices then differ only by the factor `n / (n - 1)`. -/
theorem sampleCov_eq_smul_secondMoment_of_colMean_eq_zero (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : colMean X = 0) (hn : 2 ≤ n) :
    sampleCov X = ((n : ℝ) / ((n : ℝ) - 1)) • secondMoment X := by
  rw [sampleCov_eq_secondMoment X hn, hX]
  simp

/-! ### Invariances of the centered covariance -/

/-- Shifting every sample by `c` shifts the column means by `c` (for `0 < n`). -/
theorem colMean_add_vecMulVec_one (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ) (hn : 0 < n) :
    colMean (X + vecMulVec (fun _ => 1) c) = colMean X + c := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  ext j
  simp only [colMean, Matrix.add_apply, vecMulVec_apply, one_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.add_apply]
  field_simp

/-- Centering removes a common shift `𝟙 cᵀ` of all samples. -/
theorem center_add_vecMulVec_one (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ) :
    center (X + vecMulVec (fun _ => 1) c) = center X := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i
    exact i.elim0
  · ext i j
    simp only [center, of_apply, colMean_add_vecMulVec_one X c hn, Matrix.add_apply,
      vecMulVec_apply, one_mul, Pi.add_apply]
    ring

/-- **Location invariance.** The sample covariance does not see a common shift `𝟙 cᵀ` of all
samples (the second moment does, see the test file). -/
theorem sampleCov_add_vecMulVec_one (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ) :
    sampleCov (X + vecMulVec (fun _ => 1) c) = sampleCov X := by
  simp only [sampleCov, center_add_vecMulVec_one]

/-- Centering commutes with negation. -/
theorem center_neg (X : Matrix (Fin n) (Fin p) ℝ) : center (-X) = -center X := by
  ext i j
  simp only [center, colMean, of_apply, Matrix.neg_apply, Finset.sum_neg_distrib, neg_div]
  ring

/-- **Sign invariance.** `S(-X) = S(X)`: the covariance does not see the sign of a shift. -/
theorem sampleCov_neg (X : Matrix (Fin n) (Fin p) ℝ) : sampleCov (-X) = sampleCov X := by
  simp only [sampleCov, center_neg, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-! ### Rank and singularity -/

/-- The centered columns sum to zero: `𝟙ᵀ (X - 𝟙 x̄ᵀ) = 0`. -/
theorem one_vecMul_center (X : Matrix (Fin n) (Fin p) ℝ) : (fun _ => (1 : ℝ)) ᵥ* center X = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext j
    simp [vecMul, dotProduct]
  · ext j
    simp [vecMul, dotProduct, sum_center X hn j]

/-- **Centering loses a dimension.** `rank (X - 𝟙 x̄ᵀ) ≤ n - 1`, because `𝟙` is in the left
kernel. -/
theorem rank_center_le (X : Matrix (Fin n) (Fin p) ℝ) : (center X).rank ≤ n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (rank_le_height _).trans (by simp)
  · rw [← rank_transpose]
    have hker : Submodule.span ℝ {(fun _ => (1 : ℝ))} ≤
        LinearMap.ker (center X)ᵀ.mulVecLin := by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, mulVecLin_apply,
        mulVec_transpose]
      exact one_vecMul_center X
    have h1 : Module.finrank ℝ (Submodule.span ℝ {(fun _ : Fin n => (1 : ℝ))}) = 1 :=
      finrank_span_singleton fun h => by simpa using congrFun h ⟨0, hn⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker (center X)ᵀ.mulVecLin
    have hmono := Submodule.finrank_mono hker
    rw [Module.finrank_fin_fun] at hrn
    unfold Matrix.rank
    omega

/-- With at most one sample the centered matrix vanishes (the single sample is its own
mean). -/
theorem center_eq_zero_of_le_one (X : Matrix (Fin n) (Fin p) ℝ) (hn : n ≤ 1) : center X = 0 := by
  interval_cases n
  · ext i
    exact i.elim0
  · ext i j
    fin_cases i
    simp [center, colMean]

/-- With at most one sample the sample covariance is `0`. -/
theorem sampleCov_eq_zero_of_le_one (X : Matrix (Fin n) (Fin p) ℝ) (hn : n ≤ 1) :
    sampleCov X = 0 := by
  simp [sampleCov, center_eq_zero_of_le_one X hn]

/-- `rank S = rank (X - 𝟙 x̄ᵀ)`, for every `n` (both are `0` when `n ≤ 1`). -/
theorem rank_sampleCov (X : Matrix (Fin n) (Fin p) ℝ) :
    (sampleCov X).rank = (center X).rank := by
  rcases le_or_gt 2 n with hn | hn
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h : ((n : ℝ) - 1)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
    rw [sampleCov, rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero h),
      rank_transpose_mul_self]
  · rw [sampleCov_eq_zero_of_le_one X (by omega), center_eq_zero_of_le_one X (by omega), rank_zero,
      rank_zero]

/-- `rank S ≤ n - 1` for every `n`. -/
theorem rank_sampleCov_le (X : Matrix (Fin n) (Fin p) ℝ) : (sampleCov X).rank ≤ n - 1 :=
  (rank_sampleCov X).le.trans (rank_center_le X)

/-- **High-dimensional boundary case.** With no more samples than features (`n ≤ p`, the usual
omics regime), the sample covariance is singular. -/
theorem det_sampleCov_eq_zero_of_le (X : Matrix (Fin n) (Fin p) ℝ) (hnp : n ≤ p) (hp : 0 < p) :
    (sampleCov X).det = 0 := by
  by_contra h
  have h1 := rank_of_det_ne_zero h
  have h2 := rank_sampleCov_le X
  simp only [Fintype.card_fin] at h1
  omega

/-- `(X - 𝟙 x̄ᵀ) w = X w - (x̄ ⬝ w) 𝟙`. -/
theorem center_mulVec (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin p → ℝ) :
    center X *ᵥ w = X *ᵥ w - fun _ => colMean X ⬝ᵥ w := by
  ext i
  simp [center, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- The mean of the projections `X w` is `x̄ ⬝ w`: `∑ᵢ (X w)ᵢ = n (x̄ ⬝ w)`. -/
theorem sum_mulVec (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin p → ℝ) :
    ∑ i, (X *ᵥ w) i = n * (colMean X ⬝ᵥ w) := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, sum_eq_mul_colMean, mul_assoc]

/-- `S w = 0` iff `(X - 𝟙 x̄ᵀ) w = 0`, for every `n` (both sides hold when `n ≤ 1`). -/
theorem sampleCov_mulVec_eq_zero_iff_center (X : Matrix (Fin n) (Fin p) ℝ)
    (w : Fin p → ℝ) : sampleCov X *ᵥ w = 0 ↔ center X *ᵥ w = 0 := by
  rcases le_or_gt 2 n with hn | hn
  swap
  · simp [sampleCov_eq_zero_of_le_one X (by omega), center_eq_zero_of_le_one X (by omega)]
  constructor
  · intro h
    have hq := sampleVar_scores X w
    rw [h, dotProduct_zero] at hq
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : ((n : ℝ) - 1)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
    have hsum : ∑ i, scores X w i ^ 2 = 0 := (mul_eq_zero.mp hq).resolve_left hpos
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (scores X w i)).mp hsum
    ext i
    simpa [scores] using hi i (Finset.mem_univ _)
  · intro h
    rw [sampleCov, Matrix.smul_mulVec, ← mulVec_mulVec, h, mulVec_zero, smul_zero]

/-- **Null directions of `S`.** `S w = 0` iff every sample has the same projection `c` on `w`,
i.e. the samples lie in the affine hyperplane `{x | x ⬝ w = c}` (for every `n`; trivially true
for `n ≤ 1`). -/
theorem sampleCov_mulVec_eq_zero_iff (X : Matrix (Fin n) (Fin p) ℝ)
    (w : Fin p → ℝ) : sampleCov X *ᵥ w = 0 ↔ ∃ c : ℝ, X *ᵥ w = fun _ => c := by
  rw [sampleCov_mulVec_eq_zero_iff_center X, center_mulVec, sub_eq_zero]
  constructor
  · intro h
    exact ⟨_, h⟩
  · rintro ⟨c, hc⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · funext i
      exact i.elim0
    have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm : colMean X ⬝ᵥ w = c := by
      have h1 := sum_mulVec X w
      rw [hc] at h1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      exact (mul_left_cancel₀ h0 h1).symm
    rw [hc, hm]

/-- **Singular covariance.** `det S = 0` iff the samples lie in an affine hyperplane
`{x | x ⬝ w = c}` with `w ≠ 0` (for every `n`). Contrast: `det (Xᵀ X) = 0` iff they lie in a
hyperplane through the origin, so data on an affine hyperplane missing the origin have a
singular `S` but a nonsingular second moment (see the test file). -/
theorem det_sampleCov_eq_zero_iff (X : Matrix (Fin n) (Fin p) ℝ) :
    (sampleCov X).det = 0 ↔ ∃ w ≠ 0, ∃ c : ℝ, X *ᵥ w = fun _ => c := by
  rw [← exists_mulVec_eq_zero_iff]
  simp_rw [sampleCov_mulVec_eq_zero_iff X]

/-- **Positive definite covariance.** `S` is positive definite iff no affine hyperplane
`{x | x ⬝ w = c}` (`w ≠ 0`) contains all samples (for every `n`). -/
theorem posDef_sampleCov_iff (X : Matrix (Fin n) (Fin p) ℝ) :
    (sampleCov X).PosDef ↔ ∀ w ≠ 0, ∀ c : ℝ, X *ᵥ w ≠ fun _ => c := by
  rw [(sampleCov_posSemidef X).posDef_iff_det_ne_zero, Ne, det_sampleCov_eq_zero_iff X]
  push Not
  rfl

/-- The centering-matrix form `X - 𝟙 x̄ᵀ = (1 - n⁻¹ 𝟙 𝟙ᵀ) X`. -/
theorem center_eq_centering_mul (X : Matrix (Fin n) (Fin p) ℝ) :
    center X = (1 - (n : ℝ)⁻¹ • vecMulVec (fun _ => (1 : ℝ)) (fun _ => 1)) * X := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul, center_eq_sub_vecMulVec]
  congr 1
  ext i j
  simp [vecMulVec_apply, vecMul, dotProduct, colMean, div_eq_inv_mul]

/-- **Centering does not raise the rank.** `rank (X - 𝟙 x̄ᵀ) ≤ rank X`. -/
theorem rank_center_le_rank (X : Matrix (Fin n) (Fin p) ℝ) : (center X).rank ≤ X.rank := by
  rw [center_eq_centering_mul]
  exact rank_mul_le_right _ _

/-- Subadditivity of the rank, for real matrices. This duplicates the private `rank_add_bound`
in `MathlibExt.Probability.Statistics.PCA` (Mathlib has no `Matrix.rank_add_le`); it can be
replaced once that lemma is made public, which is outside this file's scope. -/
private theorem rank_add_le' (A B : Matrix (Fin n) (Fin p) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- **Centering lowers the rank by at most one.** `rank X ≤ rank (X - 𝟙 x̄ᵀ) + 1`. The drop
happens, e.g., for identical nonzero samples (`rank X = 1`, `S = 0`; see the test file). -/
theorem rank_le_rank_center_add_one (X : Matrix (Fin n) (Fin p) ℝ) :
    X.rank ≤ (center X).rank + 1 := by
  have hX : X = center X + vecMulVec (fun _ => 1) (colMean X) := by
    rw [center_eq_sub_vecMulVec, sub_add_cancel]
  calc X.rank = (center X + vecMulVec (fun _ => 1) (colMean X)).rank := by rw [← hX]
    _ ≤ (center X).rank + (vecMulVec (fun _ => (1 : ℝ)) (colMean X)).rank := rank_add_le' _ _
    _ ≤ (center X).rank + 1 := by gcongr; exact rank_vecMulVec_le _ _

/-! ### A confounded batch design -/

/-- **Additive batch/biology design.** The samples × features matrix
`X = E + 𝟙 μᵀ + b βᵀ + s δᵀ`: a residual matrix `E`, a feature-wise baseline `μ`, a batch
covariate `b` (e.g. the batch indicator) with batch effect `β`, and a biological covariate `s`
(e.g. the condition indicator) with biological signal `δ`. The design is *confounded* when
`s = b`, i.e. every sample of one condition was processed in one batch. -/
noncomputable def batchModel (E : Matrix (Fin n) (Fin p) ℝ) (μ : Fin p → ℝ) (b s : Fin n → ℝ)
    (β δ : Fin p → ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  E + vecMulVec (fun _ => 1) μ + vecMulVec b β + vecMulVec s δ

/-- The sample covariance of the design does not depend on the baseline `μ`. -/
theorem sampleCov_batchModel_baseline (E : Matrix (Fin n) (Fin p) ℝ) (μ μ' : Fin p → ℝ)
    (b s : Fin n → ℝ) (β δ : Fin p → ℝ) :
    sampleCov (batchModel E μ b s β δ) = sampleCov (batchModel E μ' b s β δ) := by
  have h : ∀ ν, batchModel E ν b s β δ =
      (E + vecMulVec b β + vecMulVec s δ) + vecMulVec (fun _ => 1) ν := by
    intro ν
    simp only [batchModel]
    abel
  rw [h, h, sampleCov_add_vecMulVec_one, sampleCov_add_vecMulVec_one]

/-- `u 0ᵀ = 0` for a rectangular outer product (Mathlib's `vecMulVec_zero` needs both vectors
on the same index type). -/
private theorem vecMulVec_zero' (u : Fin n → ℝ) : vecMulVec u (0 : Fin p → ℝ) = 0 := by
  ext i j
  simp [vecMulVec_apply]

/-- In a confounded design the data depend on `(β, δ)` only through `β + δ`. -/
theorem batchModel_confounded (E : Matrix (Fin n) (Fin p) ℝ) (μ : Fin p → ℝ) (b : Fin n → ℝ)
    (β δ : Fin p → ℝ) : batchModel E μ b b β δ = batchModel E μ b b (β + δ) 0 := by
  simp only [batchModel, vecMulVec_add, vecMulVec_zero', add_zero, add_assoc]

/-- **Confounded designs, same covariance.** If `β + δ = β' + δ'`, the two parameter settings
`(μ, β, δ)` and `(μ', β', δ')` give the same centered sample covariance. -/
theorem sampleCov_batchModel_eq_of_add_eq (E : Matrix (Fin n) (Fin p) ℝ) (μ μ' : Fin p → ℝ)
    (b : Fin n → ℝ) {β δ β' δ' : Fin p → ℝ} (h : β + δ = β' + δ') :
    sampleCov (batchModel E μ b b β δ) = sampleCov (batchModel E μ' b b β' δ') := by
  rw [sampleCov_batchModel_baseline E μ μ', batchModel_confounded,
    batchModel_confounded E μ' b β' δ', h]

/-- **Batch effect nonidentifiable.** In a confounded design (with at least one feature) no
function of the centered sample covariance recovers the batch effect `β`: "all batch"
`(β, δ) = (a, 0)` and "all biology" `(β, δ) = (0, a)` give the same `S`. Compare
`MathlibExt.Biology.Omics.Pseudobulk.not_identifiable_of_confounded`: the scalar cell-level
hierarchical model (donor-level covariates), for the condition effect `τ` and the full data
law. -/
theorem not_exists_batch_estimator (hp : 0 < p) (E : Matrix (Fin n) (Fin p) ℝ)
    (μ : Fin p → ℝ) (b : Fin n → ℝ) :
    ¬ ∃ f : Matrix (Fin p) (Fin p) ℝ → Fin p → ℝ,
      ∀ β δ, f (sampleCov (batchModel E μ b b β δ)) = β := by
  rintro ⟨f, hf⟩
  have h1 := hf (Pi.single ⟨0, hp⟩ 1) 0
  rw [sampleCov_batchModel_eq_of_add_eq E μ μ b (β' := 0) (δ' := Pi.single ⟨0, hp⟩ 1)
    (by simp), hf] at h1
  simpa using congrFun h1 ⟨0, hp⟩

/-- **Biological signal nonidentifiable.** Likewise no function of `S` recovers `δ`. -/
theorem not_exists_signal_estimator (hp : 0 < p) (E : Matrix (Fin n) (Fin p) ℝ)
    (μ : Fin p → ℝ) (b : Fin n → ℝ) :
    ¬ ∃ f : Matrix (Fin p) (Fin p) ℝ → Fin p → ℝ,
      ∀ β δ, f (sampleCov (batchModel E μ b b β δ)) = δ := by
  rintro ⟨f, hf⟩
  have h1 := hf 0 (Pi.single ⟨0, hp⟩ 1)
  rw [sampleCov_batchModel_eq_of_add_eq E μ μ b (β' := Pi.single ⟨0, hp⟩ 1) (δ' := 0)
    (by simp), hf] at h1
  simpa using congrFun h1 ⟨0, hp⟩

/-- Centering a rank-one matrix `u vᵀ` centers `u`. -/
theorem center_vecMulVec (u : Fin n → ℝ) (v : Fin p → ℝ) :
    center (vecMulVec u v) = vecMulVec (fun i => u i - (∑ k, u k) / n) v := by
  ext i j
  simp only [center, colMean, of_apply, vecMulVec_apply, ← Finset.sum_mul]
  ring

/-- The sample covariance of a rank-one matrix `u vᵀ` is `var(u) • v vᵀ` (of rank at most one,
see `rank_sampleCov_vecMulVec_le`). -/
theorem sampleCov_vecMulVec (u : Fin n → ℝ) (v : Fin p → ℝ) :
    sampleCov (vecMulVec u v) =
      (((n : ℝ) - 1)⁻¹ * ∑ i, (u i - (∑ k, u k) / n) ^ 2) • vecMulVec v v := by
  rw [sampleCov, center_vecMulVec, transpose_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_smul,
    smul_smul]
  simp [dotProduct, sq]

/-- **What `S` does see.** Without residual noise, the covariance of a confounded design is
`var(b) • (β + δ)(β + δ)ᵀ`: the combined effect `β + δ` is visible (when `b` is not constant),
only the split is not; `S` has rank at most one
(`rank_sampleCov_batchModel_confounded_noiseless_le`), a singular boundary case for `2 ≤ p`. -/
theorem sampleCov_batchModel_confounded_noiseless (μ : Fin p → ℝ) (b : Fin n → ℝ)
    (β δ : Fin p → ℝ) :
    sampleCov (batchModel 0 μ b b β δ) =
      (((n : ℝ) - 1)⁻¹ * ∑ i, (b i - (∑ k, b k) / n) ^ 2) • vecMulVec (β + δ) (β + δ) := by
  rw [sampleCov_batchModel_baseline 0 μ 0, batchModel_confounded, ← sampleCov_vecMulVec]
  simp [batchModel, vecMulVec_zero']

/-- The sample covariance of a rank-one matrix `u vᵀ` has rank at most one. -/
theorem rank_sampleCov_vecMulVec_le (u : Fin n → ℝ) (v : Fin p → ℝ) :
    (sampleCov (vecMulVec u v)).rank ≤ 1 := by
  rw [sampleCov_vecMulVec, ← smul_one_mul]
  exact (rank_mul_le_right _ _).trans (rank_vecMulVec_le _ _)

/-- The noiseless covariance of a confounded design has rank at most one. -/
theorem rank_sampleCov_batchModel_confounded_noiseless_le (μ : Fin p → ℝ) (b : Fin n → ℝ)
    (β δ : Fin p → ℝ) : (sampleCov (batchModel 0 μ b b β δ)).rank ≤ 1 := by
  rw [sampleCov_batchModel_baseline 0 μ 0, batchModel_confounded]
  simpa [batchModel, vecMulVec_zero'] using rank_sampleCov_vecMulVec_le b (β + δ)

end MathlibExt.Biology.Omics.CovarianceBridge
