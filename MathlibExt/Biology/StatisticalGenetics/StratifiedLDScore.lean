/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScore
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Stratified LD-score regression with per-SNP variances

Stratified LD-score regression (S-LDSC, Finucane et al. 2015) lets the per-SNP heritability vary
with functional annotations. We work, as in `LDScore`, at the level of raw second moments and
conditional on the genotype matrix `X : Matrix (Fin N) (Fin M) ℝ`, but give each marker `k` its
own effect variance `σ²_k`:

  `∫ β k * β l = σ²_k * [k = l]`,  `∫ ε i * ε i' = σ²_e * [i = i']`,  `∫ β k * ε i = 0`.

* `Model.integral_chiSq`: for every genotype matrix
  `𝔼[χ²_j] = N ∑_k r_jk² σ²_k + σ²_e (∑_i X_ij²) / N`; for a standardized column the last term
  is `σ²_e`. With `σ²_k = h² / M` and `σ²_e = 1 - h²` this is `LDScore.Model.integral_chiSq`
  (`Model.ofLDScore`).
* `Model.integral_chiSq_of_annot`: if `σ²_k = ∑_C τ_C a_{kC}` for annotations `a` (binary
  categories as in Finucane et al. 2015, or continuous-valued annotations as in Gazal et al.
  2017), then `𝔼[χ²_j] = N ∑_C τ_C ℓ(j, C) + σ²_e` with the annotation LD scores
  `ℓ(j, C) = ∑_k a_{kC} r_jk²` (`annotLDScore`).
* `Model.integral_chiSq_of_alpha`: the frequency-dependent "α model" of Schoech et al. (2019),
  in which the per-allele effect variance is proportional to `[p(1 - p)]^α`, so that the
  variance of the effect of a standardized genotype is `σ²_k = c [p_k (1 - p_k)]^(1 + α)`; this is
  the case of one continuous annotation `[p_k (1 - p_k)]^(1 + α)`.
* `catH2`, `enrichment`, `sum_size_mul_enrichment`: the heritability `h²(C) = ∑_{k ∈ C} σ²_k` of
  a category, its enrichment `(h²(C) / h²) / (M_C / M)`, and the identity
  `∑_C (M_C / M) * Enrichment(C) = 1` for a partition of the markers into categories (when the
  total heritability `h² = ∑_k σ²_k` is nonzero).
* `injective_mulVec_iff_rank_eq_card`, `Model.integral_chiSq_eq_design_mulVec`: with a free
  intercept, the expected statistics `j ↦ 𝔼[χ²_j]` are the image of the parameter vector
  `(σ²_e, τ)` under the design matrix `[1 | N ℓ(·, C)]`; two parameter vectors give the same
  expected statistics for every marker iff they are equal, for all parameters, exactly when the
  design matrix has full column rank.
* `sigma2_sub_sigma2_eq`: for LDSC-SEG (Finucane et al. 2018), with an annotation for a gene set
  `S` included in the control annotation for all genes `G`, `τ_S` is the difference between the
  per-SNP variance of a SNP in `S` and that of a SNP in `G ∖ S` with the same values of all
  other annotations. The coefficient `τ_S` reported after conditioning on the other annotations
  is the partialled-out coefficient of `Matrix.frischWaughLovell`.

Divisions by `N`, `M`, `M_C` and `h²` follow the convention `x / 0 = 0`; the hypotheses of each
theorem say when this matters.

## Main results

* `Model`, `Model.integral_chiSq`, `Model.integral_chiSq_of_standardized`.
* `annotLDScore`, `Model.integral_chiSq_of_annot`, `Model.integral_chiSq_of_alpha`.
* `catH2`, `enrichment`, `sum_size_mul_enrichment`.
* `design`, `Model.integral_chiSq_eq_design_mulVec`, `injective_mulVec_iff_rank_eq_card`.
* `sigma2_sub_sigma2_eq`.

## References

* H. K. Finucane, B. Bulik-Sullivan, A. Gusev, G. Trynka, Y. Reshef, P.-R. Loh, et al.,
  *Partitioning heritability by functional annotation using genome-wide association summary
  statistics*, Nat. Genet. 47 (2015), 1228–1235.
* S. Gazal, H. K. Finucane, N. A. Furlotte, P.-R. Loh, P. F. Palamara, X. Liu, et al.,
  *Linkage disequilibrium–dependent architecture of human complex traits shows action of
  negative selection*, Nat. Genet. 49 (2017), 1421–1427.
* A. P. Schoech, D. M. Jordan, P.-R. Loh, S. Gazal, L. J. O'Connor, D. J. Balick, et al.,
  *Quantification of frequency-dependent genetic architectures in 25 UK Biobank traits reveals
  action of negative selection*, Nat. Commun. 10 (2019), 790.
* H. K. Finucane, Y. A. Reshef, V. Anttila, K. Slowikowski, A. Gusev, A. Byrnes, et al.,
  *Heritability enrichment of specifically expressed genes identifies disease-relevant tissues
  and cell types*, Nat. Genet. 50 (2018), 621–629.
-/

@[expose] public section

open MeasureTheory Matrix

namespace MathlibExt.Biology.StatisticalGenetics.StratifiedLDScore

open LDScore

variable {N M : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- The random-effects model of stratified LD-score regression at the level of raw second
moments: marker `k` has effect variance `sigma2 k`, the noise has variance `sigmaE2`, and
effects and noise are orthogonal in `L²`. As in `LDScore.Model`, the measure is arbitrary, no
means are assumed, and all statements are conditional on the genotype matrix. -/
structure Model (μ : Measure Ω) (N M : ℕ) where
  /-- The per-marker effect variance `σ²_k`. -/
  sigma2 : Fin M → ℝ
  /-- The noise variance `σ²_e`. -/
  sigmaE2 : ℝ
  /-- Random per-marker effect sizes. -/
  beta : Fin M → Ω → ℝ
  /-- Random environmental noise. -/
  eps : Fin N → Ω → ℝ
  /-- Effects are square integrable. -/
  memLp_beta : ∀ k, MemLp (beta k) 2 μ
  /-- Noise terms are square integrable. -/
  memLp_eps : ∀ i, MemLp (eps i) 2 μ
  /-- Raw second moments of the effects: `∫ β βᵀ = diag σ²`. -/
  integral_beta_mul : ∀ k l, ∫ ω, beta k ω * beta l ω ∂μ = if k = l then sigma2 k else 0
  /-- Raw second moments of the noise: `∫ ε εᵀ = σ²_e I`. -/
  integral_eps_mul : ∀ i i', ∫ ω, eps i ω * eps i' ω ∂μ = if i = i' then sigmaE2 else 0
  /-- Effects and noise are orthogonal in `L²`. -/
  integral_beta_mul_eps : ∀ k i, ∫ ω, beta k ω * eps i ω ∂μ = 0

namespace Model

variable {μ : Measure Ω} (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)

/-- The phenotype `y = X β + ε`. -/
def pheno (i : Fin N) (ω : Ω) : ℝ := ∑ k, X i k * D.beta k ω + D.eps i ω

/-- The `N`-normalized score `β̂ j = X_jᵀ y / N` of marker `j` (as in `LDScore.Model.betaHat`). -/
noncomputable def betaHat (j : Fin M) (ω : Ω) : ℝ := (∑ i, X i j * D.pheno X i ω) / N

/-- The association statistic `χ² j = N * β̂ j ^ 2` of marker `j`. -/
noncomputable def chiSq (j : Fin M) (ω : Ω) : ℝ := N * D.betaHat X j ω ^ 2

/-- The LD-score regression model of `LDScore` is the stratified model with equal per-marker
variances `h² / M` and noise variance `1 - h²`. -/
noncomputable def ofLDScore (D : LDScore.Model μ N M) : Model μ N M where
  sigma2 := fun _ => D.h2 / M
  sigmaE2 := 1 - D.h2
  beta := D.beta
  eps := D.eps
  memLp_beta := D.memLp_beta
  memLp_eps := D.memLp_eps
  integral_beta_mul := D.integral_beta_mul
  integral_eps_mul := D.integral_eps_mul
  integral_beta_mul_eps := D.integral_beta_mul_eps

/-- The stratified statistic of `ofLDScore D` is the statistic of `LDScore`. -/
theorem chiSq_ofLDScore (D : LDScore.Model μ N M) : (ofLDScore D).chiSq X = D.chiSq X := rfl

private theorem integral_weighted_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (a b : ι → ℝ) (hf : ∀ k, MemLp (f k) 2 μ)
    (hm : ∀ k l, ∫ ω, f k ω * f l ω ∂μ = if k = l then b k else 0) :
    ∫ ω, (∑ k, a k * f k ω) ^ 2 ∂μ = ∑ k, a k ^ 2 * b k := by
  classical
  have hp (k l : ι) : Integrable (fun ω => (a k * a l) * (f k ω * f l ω)) μ :=
    ((hf k).integrable_mul (hf l)).const_mul _
  have he (ω : Ω) : (∑ k, a k * f k ω) ^ 2 =
      ∑ k, ∑ l, (a k * a l) * (f k ω * f l ω) := by
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ => hp k l))]
  simp_rw [integral_finsetSum Finset.univ (fun l _ => hp _ l)]
  simp_rw [integral_const_mul, hm, mul_ite, mul_zero]
  simp [pow_two]

private theorem betaHat_eq_sum (j : Fin M) (ω : Ω) :
    D.betaHat X j ω =
      ∑ k, ldCorr X j k * D.beta k ω + ∑ i, (X i j / N) * D.eps i ω := by
  unfold betaHat pheno ldCorr
  simp_rw [mul_add, Finset.sum_add_distrib, add_div, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, div_mul_eq_mul_div, Finset.sum_div]

/-- **Expected statistic with per-marker variances**, for an arbitrary genotype matrix:
`𝔼[χ² j] = N ∑_k r_jk² σ²_k + σ²_e (∑_i X_ij²) / N`. (For `N = 0` both sides are `0`.) -/
theorem integral_chiSq (j : Fin M) :
    ∫ ω, D.chiSq X j ω ∂μ =
      N * ∑ k, ldCorr X j k ^ 2 * D.sigma2 k + D.sigmaE2 * (∑ i, X i j ^ 2) / N := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [chiSq, ldCorr]
  let f : Fin M ⊕ Fin N → Ω → ℝ := Sum.elim D.beta D.eps
  let a : Fin M ⊕ Fin N → ℝ := Sum.elim (ldCorr X j) (fun i => X i j / N)
  let b : Fin M ⊕ Fin N → ℝ := Sum.elim D.sigma2 (fun _ => D.sigmaE2)
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
  have he := integral_weighted_sq f a b hf hm
  simp only [Fintype.sum_sum_type, a, b, f, Sum.elim_inl, Sum.elim_inr] at he
  simp_rw [chiSq, betaHat_eq_sum]
  rw [integral_const_mul, he]
  simp_rw [div_pow, ← Finset.sum_mul, ← Finset.sum_div]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

/-- For a column with sum of squares `N` (a standardized marker) and `N ≠ 0`:
`𝔼[χ² j] = N ∑_k r_jk² σ²_k + σ²_e`. -/
theorem integral_chiSq_of_standardized (hN : N ≠ 0) (j : Fin M) (hX : IsStandardized X) :
    ∫ ω, D.chiSq X j ω ∂μ = N * ∑ k, ldCorr X j k ^ 2 * D.sigma2 k + D.sigmaE2 := by
  rw [D.integral_chiSq X j, (hX j).2, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hN)]

end Model

/-- The LD score of marker `j` with respect to annotation `C`:
`ℓ(j, C) = ∑_k a_{kC} r_jk²` (Finucane et al. 2015 for binary annotations; Gazal et al. 2017 for
continuous ones). -/
noncomputable def annotLDScore {ι : Type*} (X : Matrix (Fin N) (Fin M) ℝ) (a : Fin M → ι → ℝ)
    (j : Fin M) (C : ι) : ℝ :=
  ∑ k, a k C * ldCorr X j k ^ 2

namespace Model

variable {μ : Measure Ω} (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)

/-- **Stratified LD-score regression** (Finucane et al. 2015; continuous annotations, Gazal et
al. 2017): if the per-marker variances are linear in the annotations, `σ²_k = ∑_C τ_C a_{kC}`,
then for a standardized genotype matrix and `N ≠ 0`,
`𝔼[χ² j] = N ∑_C τ_C ℓ(j, C) + σ²_e`. -/
theorem integral_chiSq_of_annot {ι : Type*} [Fintype ι] (a : Fin M → ι → ℝ) (τ : ι → ℝ)
    (hσ : ∀ k, D.sigma2 k = ∑ C, τ C * a k C) (hN : N ≠ 0) (j : Fin M)
    (hX : IsStandardized X) :
    ∫ ω, D.chiSq X j ω ∂μ = N * ∑ C, τ C * annotLDScore X a j C + D.sigmaE2 := by
  rw [D.integral_chiSq_of_standardized X hN j hX]
  congr 2
  simp_rw [hσ, annotLDScore, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Frequency-dependent architecture** (the α model of Schoech et al. 2019): if the per-allele
effect variance of marker `k` with allele frequency `p_k` is proportional to `[p_k (1 - p_k)]^α`,
the variance of the effect of the standardized genotype is `σ²_k = c [p_k (1 - p_k)]^(1 + α)`,
and then, for a standardized genotype matrix and `N ≠ 0`,
`𝔼[χ² j] = N c ∑_k [p_k (1 - p_k)]^(1 + α) r_jk² + σ²_e`. (The real power is meaningful for
`0 < p_k < 1`.) -/
theorem integral_chiSq_of_alpha (p : Fin M → ℝ) (α c : ℝ)
    (hσ : ∀ k, D.sigma2 k = c * (p k * (1 - p k)) ^ (1 + α)) (hN : N ≠ 0) (j : Fin M)
    (hX : IsStandardized X) :
    ∫ ω, D.chiSq X j ω ∂μ =
      N * c * ∑ k, (p k * (1 - p k)) ^ (1 + α) * ldCorr X j k ^ 2 + D.sigmaE2 := by
  rw [D.integral_chiSq_of_annot X (fun k (_ : Unit) => (p k * (1 - p k)) ^ (1 + α))
    (fun _ => c) (fun k => by simp [hσ]) hN j hX]
  simp [annotLDScore, mul_assoc]

end Model

/-! ### Category heritability and enrichment -/

/-- The heritability `h²(C) = ∑_{k ∈ C} σ²_k` of category `C`, for a labeling `cat` of the
markers by categories. -/
noncomputable def catH2 {ι : Type*} [DecidableEq ι] (σ2 : Fin M → ℝ) (cat : Fin M → ι)
    (C : ι) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => cat k = C), σ2 k

/-- The number `M_C` of markers in category `C`. -/
def catSize {ι : Type*} [DecidableEq ι] (cat : Fin M → ι) (C : ι) : ℕ :=
  (Finset.univ.filter (fun k => cat k = C)).card

/-- The enrichment of category `C`: its proportion of heritability divided by its proportion of
markers, `(h²(C) / h²) / (M_C / M)` with `h² = ∑_k σ²_k` (Finucane et al. 2015). -/
noncomputable def enrichment {ι : Type*} [DecidableEq ι] (σ2 : Fin M → ℝ) (cat : Fin M → ι)
    (C : ι) : ℝ :=
  (catH2 σ2 cat C / ∑ k, σ2 k) / ((catSize cat C : ℝ) / M)

/-- For a partition of the markers into categories (a labeling `cat`) and nonzero total
heritability, the marker-proportion-weighted enrichments sum to one:
`∑_C (M_C / M) * Enrichment(C) = 1`. Empty categories contribute `0` on both sides of each
term. -/
theorem sum_size_mul_enrichment {ι : Type*} [Fintype ι] [DecidableEq ι] (σ2 : Fin M → ℝ)
    (cat : Fin M → ι) (hh : ∑ k, σ2 k ≠ 0) :
    ∑ C, ((catSize cat C : ℝ) / M) * enrichment σ2 cat C = 1 := by
  have hterm (C : ι) : ((catSize cat C : ℝ) / M) * enrichment σ2 cat C =
      catH2 σ2 cat C / ∑ k, σ2 k := by
    unfold enrichment
    by_cases hC : catSize cat C = 0
    · have hempty : Finset.univ.filter (fun k => cat k = C) = ∅ := Finset.card_eq_zero.mp hC
      simp [hC, catH2, hempty]
    · have hM : (M : ℝ) ≠ 0 := by
        have : 0 < catSize cat C := Nat.pos_of_ne_zero hC
        have hle : catSize cat C ≤ M := by
          simpa [catSize] using Finset.card_filter_le Finset.univ (fun k => cat k = C)
        exact_mod_cast (show M ≠ 0 by omega)
      have hC' : (catSize cat C : ℝ) ≠ 0 := by exact_mod_cast hC
      field_simp
  simp_rw [hterm, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hh]
  exact Finset.sum_fiberwise Finset.univ cat σ2

/-! ### Identifiability with a free intercept -/

/-- The design matrix `[1 | N ℓ(·, C)]` of stratified LD-score regression with a free intercept;
column `none` is the intercept and column `some C` the scaled annotation LD score. -/
noncomputable def design {ι : Type*} (X : Matrix (Fin N) (Fin M) ℝ) (a : Fin M → ι → ℝ) :
    Matrix (Fin M) (Option ι) ℝ :=
  fun j c => Option.elim c 1 fun C => N * annotLDScore X a j C

/-- A real matrix has injective `mulVec` iff it has full column rank. -/
theorem injective_mulVec_iff_rank_eq_card {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) : Function.Injective A.mulVec ↔ A.rank = Fintype.card n := by
  rw [Matrix.mulVec_injective_iff, Matrix.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank]
  exact eq_comm

namespace Model

variable {μ : Measure Ω} (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)

/-- Under the annotation model, the vector of expected statistics is the design matrix applied
to the parameter vector `(σ²_e, τ)` (intercept first). Hence the parameters are determined by
the expected statistics of all markers, whatever their values, iff
`(design X a).rank = Fintype.card (Option ι)` (`injective_mulVec_iff_rank_eq_card`). -/
theorem integral_chiSq_eq_design_mulVec {ι : Type*} [Fintype ι] (a : Fin M → ι → ℝ)
    (τ : ι → ℝ) (hσ : ∀ k, D.sigma2 k = ∑ C, τ C * a k C) (hN : N ≠ 0)
    (hX : IsStandardized X) (j : Fin M) :
    ∫ ω, D.chiSq X j ω ∂μ = (design X a *ᵥ fun c => Option.elim c D.sigmaE2 τ) j := by
  rw [D.integral_chiSq_of_annot X a τ hσ hN j hX, Matrix.mulVec, dotProduct,
    Fintype.sum_option]
  simp only [design, Option.elim, one_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun C _ => ?_
  ring

end Model

/-! ### LDSC-SEG: the gene-set coefficient as a per-SNP contrast -/

/-- **LDSC-SEG contrast** (Finucane et al. 2018): for per-SNP variances
`σ²_k = ∑_C τ_C a_{kC}`, two SNPs `k`, `k'` whose annotations agree except on annotation `cS`
differ in per-SNP variance by `τ_{cS} (a_{k cS} - a_{k' cS})`. With `cS` the indicator of a gene
set `S` contained in the control gene set `G` (whose indicator is one of the other annotations),
`k ∈ S` and `k' ∈ G ∖ S` with equal values of all other annotations give
`σ²_k - σ²_{k'} = τ_S`. -/
theorem sigma2_sub_sigma2_eq {ι : Type*} [Fintype ι] (a : Fin M → ι → ℝ) (τ : ι → ℝ)
    (cS : ι) (k k' : Fin M) (hagree : ∀ C, C ≠ cS → a k C = a k' C) :
    ∑ C, τ C * a k C - ∑ C, τ C * a k' C = τ cS * (a k cS - a k' cS) := by
  classical
  rw [← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ (Finset.mem_univ cS)]
  rw [Finset.sum_eq_zero fun C hC => by rw [hagree C (Finset.ne_of_mem_erase hC), sub_self]]
  ring

end MathlibExt.Biology.StatisticalGenetics.StratifiedLDScore
