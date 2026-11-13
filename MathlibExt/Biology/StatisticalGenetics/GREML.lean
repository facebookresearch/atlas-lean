/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScore
public import Mathlib.Probability.Moments.Variance

/-!
# GRM-based heritability: Haseman–Elston regression

The SNP heritability `h²` of a quantitative trait is the fraction of phenotypic variance
explained by the genotyped markers. In the random-effects model of GCTA/GREML and LD-score
regression (Yang et al. 2010, 2017), `N` individuals with standardized genotype matrix
`X : Matrix (Fin N) (Fin M) ℝ` have phenotypes `y = X β + ε` with
`𝔼[β βᵀ] = (h² / M) I`, `𝔼[ε εᵀ] = (1 - h²) I` and `𝔼[β εᵀ] = 0`. This is exactly
`MathlibExt.Biology.StatisticalGenetics.LDScore.Model`, which is reused here; all
expectations are conditional on `X`. Writing `A = X Xᵀ / M` for the genetic relationship
matrix (GRM, `grm`), the phenotypic second-moment matrix is `h² A + (1 - h²) I`
(`integral_pheno_mul_pheno`), so for distinct individuals

  `𝔼[y_i y_j] = h² A_ij`  (`i ≠ j`, `integral_pheno_mul_pheno_of_ne`):

the phenotype cross-products are linear in the GRM entries with slope the SNP heritability.
Haseman–Elston (HE) regression (Haseman & Elston 1972; in its GRM cross-product form, Yang et
al. 2017) estimates `h²` by least squares of the cross-products `y_i y_j` on `A_ij` over the
pairs `i < j`. Since the model has no intercept, the regression is through the origin
(`heEstimate`, `heRSS_heEstimate_le`):

  `ĥ² = ∑_{i<j} A_ij y_i y_j / ∑_{i<j} A_ij²`.

It is unbiased whenever some off-diagonal GRM entry is nonzero (`integral_heEstimate`). Its
mean-squared error is at most `C / ∑_{i<j} A_ij²` when the cross-products are square
integrable and the absolute row sums of their covariance matrix are at most `C`
(`integral_heEstimate_sub_sq_le`); by Chebyshev's inequality, along a sequence of models with
such a uniform `C` and `∑_{i<j} A_ij² → ∞`, `ĥ²` converges in probability to `h²`
(`tendsto_measure_abs_heEstimate_sub_ge`).

The covariance row-sum bound is an explicit hypothesis on fourth moments of the phenotype; it
is not derived here from a distributional assumption (for Gaussian phenotypes Isserlis'
theorem expresses those covariances through `h² A + (1 - h²) I`). Implementations such as
GCTA's `--HEreg` also fit an intercept and use sample-standardized phenotypes; neither variant
is covered. The likelihood-based (REML) estimator of GREML is not formalized in this file.

## Main results

* `grm`, `pairs`, `heEstimate`, `heRSS`: the GRM, the pairs `i < j`, the HE estimator and its
  residual sum of squares.
* `heRSS_heEstimate_le`, `heRSS_eq_heRSS_heEstimate_iff`: `ĥ²` is the (unique, when
  `∑_{i<j} A_ij² ≠ 0`) least-squares slope.
* `integral_pheno_mul_pheno`, `integral_pheno_mul_pheno_of_ne`: the HE regression identity.
* `integral_heEstimate`: unbiasedness, `𝔼[ĥ²] = h²`.
* `integral_heEstimate_sub_sq_le`, `measure_abs_heEstimate_sub_ge_le`: mean-squared error and
  Chebyshev bounds.
* `tendsto_measure_abs_heEstimate_sub_ge`: consistency.

## References

* J. K. Haseman, R. C. Elston, *The investigation of linkage between a quantitative trait and
  a marker locus*, Behav. Genet. 2 (1972), 3–19.
* J. Yang, B. Benyamin, B. P. McEvoy, et al., *Common SNPs explain a large proportion of the
  heritability for human height*, Nat. Genet. 42 (2010), 565–569.
* J. Yang, J. Zeng, M. E. Goddard, N. R. Wray, P. M. Visscher, *Concepts, estimation and
  interpretation of SNP-based heritability*, Nat. Genet. 49 (2017), 1304–1310.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MathlibExt.Biology.StatisticalGenetics.GREML

open LDScore Matrix

variable {N M : ℕ}

/-- The genetic relationship matrix (GRM) of Yang et al. (2010) built from a (standardized)
genotype matrix `X : Matrix (Fin N) (Fin M) ℝ` (individuals × markers):
`A_ij = (1 / M) ∑_k X_ik X_jk`, i.e. `A = X Xᵀ / M`. -/
noncomputable def grm (X : Matrix (Fin N) (Fin M) ℝ) (i j : Fin N) : ℝ :=
  (∑ k, X i k * X j k) / M

/-- The GRM is symmetric. -/
theorem grm_comm (X : Matrix (Fin N) (Fin M) ℝ) (i j : Fin N) : grm X i j = grm X j i := by
  simp only [grm, mul_comm]

/-- The GRM is the LD-correlation matrix of the transposed genotype matrix: the same
normalized inner product, taken over markers instead of individuals. -/
theorem grm_eq_ldCorr_transpose (X : Matrix (Fin N) (Fin M) ℝ) (i j : Fin N) :
    grm X i j = ldCorr Xᵀ i j :=
  rfl

/-- The pairs `(i, j)` of individuals with `i < j`; each unordered pair of distinct individuals
appears once. These are the observations of Haseman–Elston regression. -/
def pairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

/-- A pair in `pairs N` consists of two distinct individuals. -/
theorem ne_of_mem_pairs {p : Fin N × Fin N} (hp : p ∈ pairs N) : p.1 ≠ p.2 :=
  (Finset.mem_filter.1 hp).2.ne

/-- The Haseman–Elston (cross-product) estimator: the least-squares slope, through the origin,
of the phenotype cross-products `y_i y_j` on the relationship entries `A_ij` over the pairs
`i < j`,
`ĥ² = ∑_{i<j} A_ij y_i y_j / ∑_{i<j} A_ij²`.
When `∑_{i<j} A_ij² = 0` the value is `0` by the convention `x / 0 = 0`. -/
noncomputable def heEstimate (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) : ℝ :=
  (∑ p ∈ pairs N, A p.1 p.2 * (y p.1 * y p.2)) / ∑ p ∈ pairs N, A p.1 p.2 ^ 2

/-- The residual sum of squares of Haseman–Elston regression with slope `b`:
`∑_{i<j} (y_i y_j - b A_ij)²`. -/
def heRSS (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) (b : ℝ) : ℝ :=
  ∑ p ∈ pairs N, (y p.1 * y p.2 - b * A p.1 p.2) ^ 2

/-- Pythagoras for the regression through the origin: when `∑_{i<j} A_ij² ≠ 0`,
`RSS(b) = RSS(ĥ²) + (b - ĥ²)² ∑_{i<j} A_ij²`. -/
theorem heRSS_eq (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ)
    (hS : ∑ p ∈ pairs N, A p.1 p.2 ^ 2 ≠ 0) (b : ℝ) :
    heRSS A y b = heRSS A y (heEstimate A y) +
      (b - heEstimate A y) ^ 2 * ∑ p ∈ pairs N, A p.1 p.2 ^ 2 := by
  set S := ∑ p ∈ pairs N, A p.1 p.2 ^ 2
  set T := ∑ p ∈ pairs N, A p.1 p.2 * (y p.1 * y p.2)
  set U := ∑ p ∈ pairs N, (y p.1 * y p.2) ^ 2
  have hexp (c : ℝ) : heRSS A y c = U - 2 * c * T + c ^ 2 * S := by
    simp only [heRSS, U, T, S, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hh : heEstimate A y = T / S := rfl
  rw [hexp, hexp, hh]
  field_simp
  ring

/-- The Haseman–Elston estimator minimizes the residual sum of squares. -/
theorem heRSS_heEstimate_le (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) (b : ℝ) :
    heRSS A y (heEstimate A y) ≤ heRSS A y b := by
  by_cases hS : ∑ p ∈ pairs N, A p.1 p.2 ^ 2 = 0
  · have hA : ∀ p ∈ pairs N, A p.1 p.2 = 0 := fun p hp =>
      pow_eq_zero_iff two_ne_zero |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg fun q _ => sq_nonneg _).1 hS p hp)
    apply le_of_eq
    exact Finset.sum_congr rfl fun p hp => by rw [hA p hp]; ring
  · rw [heRSS_eq A y hS b]
    have : 0 ≤ (b - heEstimate A y) ^ 2 * ∑ p ∈ pairs N, A p.1 p.2 ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith

/-- The least-squares slope is unique when `∑_{i<j} A_ij² ≠ 0`. -/
theorem heRSS_eq_heRSS_heEstimate_iff (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ)
    (hS : ∑ p ∈ pairs N, A p.1 p.2 ^ 2 ≠ 0) (b : ℝ) :
    heRSS A y b = heRSS A y (heEstimate A y) ↔ b = heEstimate A y := by
  rw [heRSS_eq A y hS b]
  constructor
  · intro h
    have h0 : (b - heEstimate A y) ^ 2 * ∑ p ∈ pairs N, A p.1 p.2 ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
    · exact absurd h hS
  · rintro rfl
    simp

/-! ### The Haseman–Elston identity -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

private theorem integral_weighted_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (a c b : ι → ℝ) (hf : ∀ k, MemLp (f k) 2 μ)
    (hm : ∀ k l, ∫ ω, f k ω * f l ω ∂μ = if k = l then b k else 0) :
    ∫ ω, (∑ k, a k * f k ω) * (∑ l, c l * f l ω) ∂μ = ∑ k, a k * c k * b k := by
  have hp (k l : ι) : Integrable (fun ω => (a k * c l) * (f k ω * f l ω)) μ :=
    ((hf k).integrable_mul (hf l)).const_mul _
  have he (ω : Ω) : (∑ k, a k * f k ω) * (∑ l, c l * f l ω) =
      ∑ k, ∑ l, (a k * c l) * (f k ω * f l ω) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ => hp k l))]
  simp_rw [integral_finsetSum Finset.univ (fun l _ => hp _ l)]
  simp_rw [integral_const_mul, hm, mul_ite, mul_zero]
  simp

/-- The phenotype `y = X β + ε` of the LD-score model is square integrable. -/
theorem memLp_pheno (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    MemLp (D.pheno X i) 2 μ := by
  have h : MemLp (fun ω => ∑ k, X i k * D.beta k ω) 2 μ :=
    memLp_finsetSum Finset.univ fun k _ => (D.memLp_beta k).const_mul _
  exact h.add (D.memLp_eps i)

/-- **The Haseman–Elston identity** (raw second moments of the phenotype). In the random-effects
model `y = X β + ε` with `𝔼[β βᵀ] = (h² / M) I`, `𝔼[ε εᵀ] = (1 - h²) I` and `𝔼[β εᵀ] = 0`
(`LDScore.Model`), for every genotype matrix `X`,
`𝔼[y_i y_j] = h² A_ij + (1 - h²) [i = j]` with the GRM `A = X Xᵀ / M`. -/
theorem integral_pheno_mul_pheno (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    (i j : Fin N) :
    ∫ ω, D.pheno X i ω * D.pheno X j ω ∂μ =
      D.h2 * grm X i j + if i = j then 1 - D.h2 else 0 := by
  classical
  let f : Fin M ⊕ Fin N → Ω → ℝ := Sum.elim D.beta D.eps
  let a : Fin N → Fin M ⊕ Fin N → ℝ := fun i =>
    Sum.elim (X i) (fun i' => if i' = i then 1 else 0)
  let b : Fin M ⊕ Fin N → ℝ := Sum.elim (fun _ => D.h2 / M) (fun _ => 1 - D.h2)
  have hf (k : Fin M ⊕ Fin N) : MemLp (f k) 2 μ := by
    cases k with
    | inl k => exact D.memLp_beta k
    | inr i => exact D.memLp_eps i
  have hm (k l : Fin M ⊕ Fin N) :
      ∫ ω, f k ω * f l ω ∂μ = if k = l then b k else 0 := by
    cases k with
    | inl k =>
      cases l with
      | inl l => simpa [f, b] using D.integral_beta_mul k l
      | inr i => simpa [f] using D.integral_beta_mul_eps k i
    | inr i =>
      cases l with
      | inl k => simpa [f, mul_comm] using D.integral_beta_mul_eps k i
      | inr i' => simpa [f, b] using D.integral_eps_mul i i'
  have hy (i : Fin N) (ω : Ω) : D.pheno X i ω = ∑ k, a i k * f k ω := by
    simp [Model.pheno, a, f, Fintype.sum_sum_type]
  simp_rw [hy]
  rw [integral_weighted_mul f (a i) (a j) b hf hm]
  simp only [Fintype.sum_sum_type, a, b, Sum.elim_inl, Sum.elim_inr, grm]
  congr 1
  · rw [← Finset.sum_mul]
    ring
  · simp_rw [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    by_cases hij : i = j <;> simp [hij]

/-- **Haseman–Elston regression identity**: for distinct individuals the expected phenotype
cross-product is linear in the GRM entry with slope the SNP heritability,
`𝔼[y_i y_j] = h² A_ij` (`i ≠ j`). -/
theorem integral_pheno_mul_pheno_of_ne (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    {i j : Fin N} (hij : i ≠ j) :
    ∫ ω, D.pheno X i ω * D.pheno X j ω ∂μ = D.h2 * grm X i j := by
  rw [integral_pheno_mul_pheno]
  simp [hij]

private theorem integrable_pheno_mul (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    (i j : Fin N) : Integrable (fun ω => D.pheno X i ω * D.pheno X j ω) μ :=
  (memLp_pheno D X i).integrable_mul (memLp_pheno D X j)

/-- **Unbiasedness of Haseman–Elston regression.** In the model of `integral_pheno_mul_pheno`,
whenever the GRM has a nonzero off-diagonal entry (`∑_{i<j} A_ij² ≠ 0`), the HE estimator
computed from the phenotypes is unbiased for the SNP heritability: `𝔼[ĥ²] = h²`. -/
theorem integral_heEstimate (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    (hS : ∑ p ∈ pairs N, grm X p.1 p.2 ^ 2 ≠ 0) :
    ∫ ω, heEstimate (grm X) (fun i => D.pheno X i ω) ∂μ = D.h2 := by
  unfold heEstimate
  rw [integral_div, integral_finsetSum _ fun p _ => (integrable_pheno_mul D X _ _).const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl fun p hp => by
    rw [integral_pheno_mul_pheno_of_ne D X (ne_of_mem_pairs hp)]]
  rw [div_eq_iff hS, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-! ### Consistency -/

/-- The estimation error of the Haseman–Elston estimator is the regression-weighted average of
the deviations of the cross-products from `h A_ij`. -/
theorem heEstimate_sub (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ)
    (hS : ∑ p ∈ pairs N, A p.1 p.2 ^ 2 ≠ 0) (h : ℝ) :
    heEstimate A y - h =
      (∑ p ∈ pairs N, A p.1 p.2 * (y p.1 * y p.2 - h * A p.1 p.2)) /
        ∑ p ∈ pairs N, A p.1 p.2 ^ 2 := by
  rw [heEstimate, eq_div_iff hS, sub_mul, div_mul_cancel₀ _ hS, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The deviation `y_i y_j - h² A_ij` of the phenotype cross-product of the pair `p = (i, j)`
from its expectation `h² A_ij` (`integral_pheno_mul_pheno_of_ne`, for `i ≠ j`). The integrals
`∫ heDev p * heDev q` are therefore the covariances of the cross-products when `μ` is a
probability measure. -/
noncomputable def heDev (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (p : Fin N × Fin N)
    (ω : Ω) : ℝ :=
  D.pheno X p.1 ω * D.pheno X p.2 ω - D.h2 * grm X p.1 p.2

/-- Schur's test for a quadratic form given by second moments: if every absolute row sum of
`K_pq = ∫ d_p d_q` is at most `C`, then `∫ (∑ w_p d_p)² ≤ C ∑ w_p²`. -/
private theorem integral_sq_sum_le {ι : Type*} (s : Finset ι) (d : ι → Ω → ℝ) (w : ι → ℝ)
    (hd : ∀ p ∈ s, MemLp (d p) 2 μ) {C : ℝ}
    (hC : ∀ p ∈ s, ∑ q ∈ s, |∫ ω, d p ω * d q ω ∂μ| ≤ C) :
    ∫ ω, (∑ p ∈ s, w p * d p ω) ^ 2 ∂μ ≤ C * ∑ p ∈ s, w p ^ 2 := by
  set K : ι → ι → ℝ := fun p q => ∫ ω, d p ω * d q ω ∂μ with hK
  have hp : ∀ p ∈ s, ∀ q ∈ s, Integrable (fun ω => (w p * w q) * (d p ω * d q ω)) μ :=
    fun p hp q hq => ((hd p hp).integrable_mul (hd q hq)).const_mul _
  have he (ω : Ω) : (∑ p ∈ s, w p * d p ω) ^ 2 =
      ∑ p ∈ s, ∑ q ∈ s, (w p * w q) * (d p ω * d q ω) := by
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp_rw [he]
  rw [integral_finsetSum s (fun p hp' => integrable_finsetSum s (fun q hq => hp p hp' q hq))]
  rw [Finset.sum_congr rfl fun p hp' => integral_finsetSum s (fun q hq => hp p hp' q hq)]
  simp_rw [integral_const_mul]
  have hKc (p q : ι) : |K p q| = |K q p| := by simp only [hK, mul_comm]
  have hterm (p q : ι) : w p * w q * K p q ≤ (w p ^ 2 * |K p q| + w q ^ 2 * |K q p|) / 2 := by
    rw [← hKc p q]
    have h1 : w p * w q * K p q ≤ |w p| * |w q| * |K p q| := by
      rw [← abs_mul, ← abs_mul]; exact le_abs_self _
    have h2 : 0 ≤ (|w p| - |w q|) ^ 2 * |K p q| := mul_nonneg (sq_nonneg _) (abs_nonneg _)
    have h5 : (|w p| - |w q|) ^ 2 * |K p q| =
        |w p| ^ 2 * |K p q| + |w q| ^ 2 * |K p q| - 2 * (|w p| * |w q| * |K p q|) := by ring
    rw [h5, sq_abs, sq_abs] at h2
    linarith
  calc ∑ p ∈ s, ∑ q ∈ s, w p * w q * K p q
      ≤ ∑ p ∈ s, ∑ q ∈ s, (w p ^ 2 * |K p q| + w q ^ 2 * |K q p|) / 2 :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = (∑ p ∈ s, w p ^ 2 * ∑ q ∈ s, |K p q| + ∑ q ∈ s, w q ^ 2 * ∑ p ∈ s, |K q p|) / 2 := by
        simp_rw [add_div, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm (f := fun p q => w q ^ 2 * |K q p| / 2)]
        simp_rw [Finset.sum_div]
    _ ≤ (∑ p ∈ s, w p ^ 2 * C + ∑ q ∈ s, w q ^ 2 * C) / 2 := by
        gcongr with p hp' q hq
        · exact hC p hp'
        · exact hC q hq
    _ = C * ∑ p ∈ s, w p ^ 2 := by
        rw [← Finset.sum_mul]; ring

/-- **Mean-squared error of Haseman–Elston regression.** If the cross-products are square
integrable and every absolute row sum of their second-moment matrix about `h² A_ij` is at most
`C` (`∑_{q} |∫ heDev p * heDev q| ≤ C` for every pair `p`), then
`𝔼[(ĥ² - h²)²] ≤ C / ∑_{i<j} A_ij²`. -/
theorem integral_heEstimate_sub_sq_le [IsFiniteMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ)
    (hS : ∑ p ∈ pairs N, grm X p.1 p.2 ^ 2 ≠ 0)
    (hmem : ∀ p ∈ pairs N, MemLp (fun ω => D.pheno X p.1 ω * D.pheno X p.2 ω) 2 μ) {C : ℝ}
    (hC : ∀ p ∈ pairs N, ∑ q ∈ pairs N, |∫ ω, heDev D X p ω * heDev D X q ω ∂μ| ≤ C) :
    ∫ ω, (heEstimate (grm X) (fun i => D.pheno X i ω) - D.h2) ^ 2 ∂μ ≤
      C / ∑ p ∈ pairs N, grm X p.1 p.2 ^ 2 := by
  set S := ∑ p ∈ pairs N, grm X p.1 p.2 ^ 2
  have hSpos : 0 < S := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hS)
  have hdev : ∀ p ∈ pairs N, MemLp (heDev D X p) 2 μ := fun p hp =>
    (hmem p hp).sub (memLp_const _)
  have hrw (ω : Ω) : (heEstimate (grm X) (fun i => D.pheno X i ω) - D.h2) ^ 2 =
      (∑ p ∈ pairs N, grm X p.1 p.2 * heDev D X p ω) ^ 2 / S ^ 2 := by
    rw [heEstimate_sub _ _ hS, div_pow]
    rfl
  simp_rw [hrw]
  rw [integral_div, div_le_div_iff₀ (by positivity) hSpos]
  calc (∫ ω, (∑ p ∈ pairs N, grm X p.1 p.2 * heDev D X p ω) ^ 2 ∂μ) * S
      ≤ (C * S) * S := by
        gcongr
        exact integral_sq_sum_le _ _ _ hdev hC
    _ = C * S ^ 2 := by ring

/-- **Chebyshev bound for Haseman–Elston regression.** Under the hypotheses of
`integral_heEstimate_sub_sq_le`, on a finite measure space,
`μ {|ĥ² - h²| ≥ ε} ≤ C / (ε² ∑_{i<j} A_ij²)`. -/
theorem measure_abs_heEstimate_sub_ge_le [IsFiniteMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hS : ∑ p ∈ pairs N, grm X p.1 p.2 ^ 2 ≠ 0)
    (hmem : ∀ p ∈ pairs N, MemLp (fun ω => D.pheno X p.1 ω * D.pheno X p.2 ω) 2 μ) {C : ℝ}
    (hC : ∀ p ∈ pairs N, ∑ q ∈ pairs N, |∫ ω, heDev D X p ω * heDev D X q ω ∂μ| ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |heEstimate (grm X) (fun i => D.pheno X i ω) - D.h2|} ≤
      ENNReal.ofReal (C / (ε ^ 2 * ∑ p ∈ pairs N, grm X p.1 p.2 ^ 2)) := by
  set Y : Ω → ℝ := fun ω => heEstimate (grm X) (fun i => D.pheno X i ω)
  have hY : MemLp Y 2 μ := by
    have h : MemLp (fun ω => ∑ p ∈ pairs N,
        grm X p.1 p.2 * (D.pheno X p.1 ω * D.pheno X p.2 ω)) 2 μ :=
      memLp_finsetSum _ fun p hp => (hmem p hp).const_mul _
    convert h.const_mul (∑ p ∈ pairs N, grm X p.1 p.2 ^ 2)⁻¹ using 1
    funext ω
    simp only [Y, heEstimate, div_eq_inv_mul]
  have hmean : μ[Y] = D.h2 := integral_heEstimate D X hS
  have hcheb := meas_ge_le_variance_div_sq hY hε
  rw [hmean] at hcheb
  refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_comm, ← div_div]
  gcongr ?_ / _
  rw [variance_eq_integral hY.aemeasurable, hmean]
  exact integral_heEstimate_sub_sq_le D X hS hmem hC

/-- **Consistency of Haseman–Elston regression.** Consider a sequence of LD-score models
(`y = X β + ε` with the GRM `A = X Xᵀ / M`) on finite measure spaces (in the application,
probability spaces), with `N n` individuals,
`M n` markers and common SNP heritability `h²`. Suppose the phenotype cross-products are square
integrable and their covariance matrix has absolute row sums bounded by a constant `C`
uniformly in `n` (a weak-dependence condition on the pairs), and the off-diagonal GRM energy
`∑_{i<j} A_ij²` tends to infinity. Then the HE estimator converges in probability to `h²`:
`μₙ {|ĥ²ₙ - h²| ≥ ε} → 0` for every `ε > 0`. -/
theorem tendsto_measure_abs_heEstimate_sub_ge {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsFiniteMeasure (μ n)] {N M : ℕ → ℕ}
    (D : ∀ n, Model (μ n) (N n) (M n)) (X : ∀ n, Matrix (Fin (N n)) (Fin (M n)) ℝ)
    {h2 C : ℝ} (hh2 : ∀ n, (D n).h2 = h2)
    (hmem : ∀ n, ∀ p ∈ pairs (N n),
      MemLp (fun ω => (D n).pheno (X n) p.1 ω * (D n).pheno (X n) p.2 ω) 2 (μ n))
    (hC : ∀ n, ∀ p ∈ pairs (N n),
      ∑ q ∈ pairs (N n), |∫ ω, heDev (D n) (X n) p ω * heDev (D n) (X n) q ω ∂(μ n)| ≤ C)
    (hS : Tendsto (fun n => ∑ p ∈ pairs (N n), grm (X n) p.1 p.2 ^ 2) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ n {ω | ε ≤
      |heEstimate (grm (X n)) (fun i => (D n).pheno (X n) i ω) - h2|}) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop, μ n {ω | ε ≤
      |heEstimate (grm (X n)) (fun i => (D n).pheno (X n) i ω) - h2|} ≤
      ENNReal.ofReal (C / (ε ^ 2 * ∑ p ∈ pairs (N n), grm (X n) p.1 p.2 ^ 2)) := by
    filter_upwards [hS.eventually_gt_atTop 0] with n hn
    have h := measure_abs_heEstimate_sub_ge_le (D n) (X n) hn.ne' (hmem n) (hC n) hε
    rwa [hh2 n] at h
  have hlim : Tendsto (fun n => ENNReal.ofReal
      (C / (ε ^ 2 * ∑ p ∈ pairs (N n), grm (X n) p.1 p.2 ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal ((hS.const_mul_atTop (pow_pos hε 2)).const_div_atTop C)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) hbound

end MathlibExt.Biology.StatisticalGenetics.GREML
