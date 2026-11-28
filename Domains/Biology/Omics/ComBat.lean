/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Defs.Filter
import MathlibExt.Probability.FiniteProbability
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# ComBat empirical Bayes location–scale batch adjustment

Johnson, Li and Rabinovic (2007) adjust gene expression data for batch effects. Let `Y i j g` be
the expression value of gene `g` for sample `j` of batch `i`, and `X` a design matrix of
biological covariates. The location–scale model is

  `Y i j g = α g + X β g + γ i g + δ i g * ε i j g`,  `ε i j g ~ N(0, σ g ^ 2)`,

with additive batch effects `γ i g` and multiplicative batch effects `δ i g > 0`. ComBat

1. standardizes each gene: it estimates `α̂ g`, `β̂ g` and raw batch effects `γ̃ i g` by
   gene-wise least squares under the constraint `∑ i, n i * γ̃ i g = 0`, sets
   `σ̂ g ^ 2 = N⁻¹ ∑ i j, (Y i j g - α̂ g - X β̂ g - γ̃ i g) ^ 2` and standardizes
   `Z i j g = (Y i j g - α̂ g - X β̂ g) / σ̂ g`;
2. models the standardized data as `Z i j g ~ N(γ' i g, δ' i g ^ 2)` with, across the genes of a
   batch, priors `γ' i g ~ N(γ i, τ i ^ 2)` and `δ' i g ^ 2 ~ Inverse-Gamma(λ i, θ i)`, whose
   hyperparameters it estimates by the method of moments from the gene-wise standardized batch
   means `γ̂' i g` and variances `δ̂' i g ^ 2`;
3. estimates `γ' i g` and `δ' i g ^ 2` by their conditional posterior means `γ* i g` and
   `δ* i g ^ 2`, which depend on each other and are solved jointly by iteration;
4. returns the adjusted data `Y* i j g = σ̂ g / δ* i g * (Z i j g - γ* i g) + α̂ g + X β̂ g`.

The posterior means shrink the gene-wise standardized batch estimates towards the batch-wide
means, which keeps the adjustment stable for small batches.

## Conventions

* Genes, batches, samples and covariates form finite types. Each sample `s` lies in the batch
  `batch s` and has the covariates `x s k`, its row of `X`, so that `X β` at `s` is
  `∑ k, x s k * β k`; `X` has no intercept column, which the batch indicators already span. The
  data are `Y g s`. `n i` is the number of samples of batch `i`, `N` the number of samples and `G`
  the number of genes.
* The least-squares fit regresses each gene on the batch indicators and the covariates
  (`olsEstimator`, `(Xᵀ X)⁻¹ Xᵀ y`, as the `sva` package does). With batch coefficients `B i`,
  `α̂ = ∑ i, (n i / N) * B i` and `γ̃ i = B i - α̂`. When the design is identifiable this is the
  unique least-squares solution under the constraint (`leastSquares_standardization`).
* The divisors are those of the supplementary material of the source (§A.3.1) and of the
  `ComBat` function of the Bioconductor `sva` package: `n i - 1` for `δ̂' i g ^ 2`, `G` for the
  means over the genes, `γ̄ i` and `V i`, and `G - 1` for the variances over the genes, `τ̄ i ^ 2`
  and `S i ^ 2`. Matching the inverse-gamma mean `θ / (λ - 1)` and variance
  `θ ^ 2 / ((λ - 1) ^ 2 * (λ - 2))` to `V i` and `S i ^ 2` gives
  `λ̄ i = (V i ^ 2 + 2 * S i ^ 2) / S i ^ 2` and `θ̄ i = (V i ^ 3 + V i * S i ^ 2) / S i ^ 2`.
* The iteration starts from `δ̂' i g ^ 2`, as the source suggests and `sva` does, and alternates
  the two conditional posterior means `γ = (n i τ̄ i ^ 2 γ̂' i g + d γ̄ i) / (n i τ̄ i ^ 2 + d)`
  and `d = (θ̄ i + ∑ j, (Z i j g - γ) ^ 2 / 2) / (n i / 2 + λ̄ i - 1)`. `δ* i g ^ 2` is the limit of
  the `d` (`limUnder`), `γ* i g` the location at it, and `δ* i g = √(δ* i g ^ 2)`. When the
  `δ̂' i g ^ 2` of batch `i` have positive variance over the genes, the limit exists, is positive
  and solves both equations (`empiricalBayes_fixedPoint`, which applies to `adjust` through
  `adjust_eq_of_standardized`).
* The definition is total, with Lean's `x / 0 = 0`. The method needs at least two samples in each
  batch, an identifiable design, `σ̂ g > 0` and, in each batch, gene-wise variances `δ̂' i g ^ 2`
  of positive variance over the genes; each theorem assumes what it uses.
* The normal and inverse-gamma priors are conjugate to the normal model of the standardized data,
  which makes the two updates the conditional posterior means (supplementary material, §A.3).
  The probability model is not formalized here: `adjust` computes the estimates and the adjusted
  data from the formulas.

## Main definition

* `adjust batch x Y`: the ComBat adjusted data.

## Main results

* `leastSquares_standardization`: the standardization's estimates are the unique least-squares
  solution under the constraint `∑ i, n i * γ̃ i = 0`.
* `empiricalBayes_fixedPoint`: when the gene-wise variances of a batch have positive variance over
  the genes, the method-of-moments hyperparameters match that mean and variance, with `λ̄ > 2`, and
  the iteration converges to a positive joint fixed point of the two conditional posterior means,
  whose location shrinks the gene-wise estimate towards the batch-wide mean.
* `adjust_update_affine`: rescaling one gene by a positive affine map leaves every other gene's
  adjustment unchanged and rescales its own in the same way.
* `adjust_eq_of_standardized`: `adjust` written through the standardized data and the estimates of
  `empiricalBayes_fixedPoint`.

## References

* W. E. Johnson, C. Li and A. Rabinovic, "Adjusting batch effects in microarray expression data
  using empirical Bayes methods", Biostatistics 8 (2007), 118–127,
  <https://doi.org/10.1093/biostatistics/kxj037>: §2.3, §3.1 (equations (2.1) and (3.1)) and the
  supplementary material, §A.3.
-/

@[expose] public section

open Filter Topology Matrix
open scoped Finset
open MathlibExt.Probability.Statistics.LinearModel

namespace Domains.Biology.Omics.ComBat

variable {Gene Batch Sample Covariate : Type*} [Fintype Gene] [Fintype Batch] [DecidableEq Batch]
  [Fintype Sample] [DecidableEq Sample] [Fintype Covariate] [DecidableEq Covariate]

/-- The **ComBat empirical Bayes location–scale batch adjustment** of Johnson, Li and Rabinovic
(2007): the adjusted expression `adjust batch x Y g s` of gene `g` in sample `s`, from the
expression values `Y g s`, the batch `batch s` of each sample and its biological covariates
`x s k`. With `n i` the number of samples of batch `i`, `N` the number of samples, `G` the number
of genes and `i = batch s`,

  `adjust batch x Y g s = σ̂ g / √(δ*² i g) * (Z g s - γ* i g) + α̂ g + ∑ k, x s k * β̂ g k`,

where:

* `B g` are the least-squares coefficients of `Y g` on the batch indicators and the covariates,
  `α̂ g = ∑ i, (n i / N) * B g i` and `γ̃ i g = B g i - α̂ g` (so `∑ i, n i * γ̃ i g = 0`), `β̂ g`
  the covariate coefficients,
  `σ̂ g = √(∑ s, (Y g s - α̂ g - ∑ k, x s k * β̂ g k - γ̃ (batch s) g) ^ 2 / N)`, and
  `Z g s = (Y g s - α̂ g - ∑ k, x s k * β̂ g k) / σ̂ g` are the standardized data;
* `γ̂' i g` and `δ̂'² i g` are the mean and the variance (divisor `n i - 1`) of the `Z g s` over
  the samples of batch `i`; `γ̄ i` and `τ̄² i` are the mean and the variance (divisor `G - 1`) of
  the `γ̂' i g` over the genes; `V i` and `S² i` are those of the `δ̂'² i g`, and
  `λ̄ i = (V i ^ 2 + 2 S² i) / S² i` and `θ̄ i = (V i ^ 3 + V i S² i) / S² i` are the
  inverse-gamma hyperparameters of the method of moments;
* `δ*² i g` is the limit of the iteration that starts at `δ̂'² i g` and maps `d` to
  `(θ̄ i + ∑ s ∈ batch i, (Z g s - γ) ^ 2 / 2) / (n i / 2 + λ̄ i - 1)` with
  `γ = (n i τ̄² i γ̂' i g + d γ̄ i) / (n i τ̄² i + d)`, and `γ* i g` is that `γ` at `d = δ*² i g`.
  These are the two conditional posterior means, which hold jointly at the limit
  (`empiricalBayes_fixedPoint` and `adjust_eq_of_standardized`).

The definition is total: a limit that does not exist and divisions by zero give junk values.
The source assumes at least two samples in each batch, an identifiable design (in particular no
intercept among the covariates), `σ̂ g > 0` and gene-wise variances `δ̂'² i g` with positive
variance `S² i` over the genes. -/
noncomputable def adjust (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (Y : Gene → Sample → ℝ) : Gene → Sample → ℝ :=
  -- the batch sizes, the number of samples and the number of genes
  let n : Batch → ℝ := fun i => #{s | batch s = i}
  let N : ℝ := Fintype.card Sample
  let G : ℝ := Fintype.card Gene
  -- standardization: gene-wise least squares on the batch indicators and the covariates
  let B : Gene → Batch ⊕ Covariate → ℝ := fun g =>
    olsEstimator (Matrix.of fun s => Sum.elim (fun i => if batch s = i then 1 else 0) (x s)) (Y g)
  let αHat : Gene → ℝ := fun g => ∑ i, n i / N * B g (.inl i)
  let βHat : Gene → Covariate → ℝ := fun g k => B g (.inr k)
  let γTilde : Batch → Gene → ℝ := fun i g => B g (.inl i) - αHat g
  let σHat : Gene → ℝ := fun g =>
    √((∑ s, (Y g s - αHat g - ∑ k, x s k * βHat g k - γTilde (batch s) g) ^ 2) / N)
  let Z : Gene → Sample → ℝ := fun g s => (Y g s - αHat g - ∑ k, x s k * βHat g k) / σHat g
  -- gene-wise estimates and the method-of-moments hyperparameters
  let γHat : Batch → Gene → ℝ := fun i g => (∑ s with batch s = i, Z g s) / n i
  let δHat2 : Batch → Gene → ℝ := fun i g =>
    (∑ s with batch s = i, (Z g s - γHat i g) ^ 2) / (n i - 1)
  let γBar : Batch → ℝ := fun i => (∑ g, γHat i g) / G
  let τBar2 : Batch → ℝ := fun i => (∑ g, (γHat i g - γBar i) ^ 2) / (G - 1)
  let V : Batch → ℝ := fun i => (∑ g, δHat2 i g) / G
  let S2 : Batch → ℝ := fun i => (∑ g, (δHat2 i g - V i) ^ 2) / (G - 1)
  let lamBar : Batch → ℝ := fun i => (V i ^ 2 + 2 * S2 i) / S2 i
  let θBar : Batch → ℝ := fun i => (V i ^ 3 + V i * S2 i) / S2 i
  -- the empirical Bayes estimates: the two conditional posterior means, iterated
  let post : Batch → Gene → ℝ → ℝ := fun i g d =>
    (n i * τBar2 i * γHat i g + d * γBar i) / (n i * τBar2 i + d)
  let next : Batch → Gene → ℝ → ℝ := fun i g d =>
    (θBar i + (∑ s with batch s = i, (Z g s - post i g d) ^ 2) / 2) / (n i / 2 + lamBar i - 1)
  let δStar2 : Batch → Gene → ℝ := fun i g => limUnder atTop fun k => (next i g)^[k] (δHat2 i g)
  let γStar : Batch → Gene → ℝ := fun i g => post i g (δStar2 i g)
  -- the adjusted data
  fun g s => σHat g / √(δStar2 (batch s) g) * (Z g s - γStar (batch s) g) + αHat g +
    ∑ k, x s k * βHat g k

/-! ### The stages of `adjust`, for the proofs -/

/-- The design matrix: the batch indicators and the covariates of each sample. -/
private def design (batch : Sample → Batch) (x : Sample → Covariate → ℝ) :
    Matrix Sample (Batch ⊕ Covariate) ℝ :=
  Matrix.of fun s => Sum.elim (fun i => if batch s = i then 1 else 0) (x s)

/-- The least-squares coefficients of `y` on the batch indicators and the covariates. -/
private noncomputable def coef (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (y : Sample → ℝ) : Batch ⊕ Covariate → ℝ :=
  olsEstimator (design batch x) y

/-- The overall level `α̂`, the batch coefficients averaged with weights `n i / N`. -/
private noncomputable def grand (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (y : Sample → ℝ) : ℝ :=
  ∑ i, (#{s | batch s = i} : ℝ) / (Fintype.card Sample : ℝ) * coef batch x y (.inl i)

/-- The pooled residual standard deviation `σ̂`. -/
private noncomputable def scale (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (y : Sample → ℝ) : ℝ :=
  √((∑ s, (y s - grand batch x y - ∑ k, x s k * coef batch x y (.inr k) -
    (coef batch x y (.inl (batch s)) - grand batch x y)) ^ 2) / (Fintype.card Sample : ℝ))

/-- The standardized data `Z`. -/
private noncomputable def stdz (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (Y : Gene → Sample → ℝ) : Gene → Sample → ℝ := fun g s =>
  (Y g s - grand batch x (Y g) - ∑ k, x s k * coef batch x (Y g) (.inr k)) /
    scale batch x (Y g)

/-- The empirical Bayes estimates `(γ*, δ*²)` computed from standardized data `Z`. -/
private noncomputable def ebStar (batch : Sample → Batch) (Z : Gene → Sample → ℝ) :
    Batch → Gene → ℝ × ℝ :=
  let n : Batch → ℝ := fun i => #{s | batch s = i}
  let G : ℝ := Fintype.card Gene
  let γHat : Batch → Gene → ℝ := fun i g => (∑ s with batch s = i, Z g s) / n i
  let δHat2 : Batch → Gene → ℝ := fun i g =>
    (∑ s with batch s = i, (Z g s - γHat i g) ^ 2) / (n i - 1)
  let γBar : Batch → ℝ := fun i => (∑ g, γHat i g) / G
  let τBar2 : Batch → ℝ := fun i => (∑ g, (γHat i g - γBar i) ^ 2) / (G - 1)
  let V : Batch → ℝ := fun i => (∑ g, δHat2 i g) / G
  let S2 : Batch → ℝ := fun i => (∑ g, (δHat2 i g - V i) ^ 2) / (G - 1)
  let lamBar : Batch → ℝ := fun i => (V i ^ 2 + 2 * S2 i) / S2 i
  let θBar : Batch → ℝ := fun i => (V i ^ 3 + V i * S2 i) / S2 i
  let post : Batch → Gene → ℝ → ℝ := fun i g d =>
    (n i * τBar2 i * γHat i g + d * γBar i) / (n i * τBar2 i + d)
  let next : Batch → Gene → ℝ → ℝ := fun i g d =>
    (θBar i + (∑ s with batch s = i, (Z g s - post i g d) ^ 2) / 2) / (n i / 2 + lamBar i - 1)
  let δStar2 : Batch → Gene → ℝ := fun i g => limUnder atTop fun k => (next i g)^[k] (δHat2 i g)
  fun i g => (post i g (δStar2 i g), δStar2 i g)

private theorem adjust_eq (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (Y : Gene → Sample → ℝ) (g : Gene) (s : Sample) :
    adjust batch x Y g s = scale batch x (Y g) / √(ebStar batch (stdz batch x Y) (batch s) g).2 *
      (stdz batch x Y g s - (ebStar batch (stdz batch x Y) (batch s) g).1) +
      grand batch x (Y g) + ∑ k, x s k * coef batch x (Y g) (.inr k) :=
  rfl

/-! ### Least squares on the batch indicators and the covariates -/

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Covariate] in
private theorem design_mulVec (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (v : Batch ⊕ Covariate → ℝ) (s : Sample) :
    (design batch x *ᵥ v) s = v (.inl (batch s)) + ∑ k, x s k * v (.inr k) := by
  simp [design, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Covariate] in
private theorem injective_design {batch : Sample → Batch} {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0) :
    Function.Injective (design batch x).mulVec := by
  intro v w hvw
  have h0 : ∀ s, (v - w) (.inl (batch s)) + ∑ k, x s k * (v - w) (.inr k) = 0 := by
    intro s
    rw [← design_mulVec, mulVec_sub, hvw, sub_self, Pi.zero_apply]
  obtain ⟨hb, hc⟩ := hident (fun i => (v - w) (.inl i)) (fun k => (v - w) (.inr k)) h0
  funext j
  rcases j with i | k
  · simpa [sub_eq_zero] using congr_fun hb i
  · simpa [sub_eq_zero] using congr_fun hc k

omit [DecidableEq Sample] in
private theorem isUnit_design {batch : Sample → Batch} {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0) :
    IsUnit ((design batch x)ᵀ * design batch x) :=
  (MathlibExt.Probability.FiniteProbability.isUnit_transpose_mul_self_iff _).mpr
    (Matrix.mulVec_injective_iff.mp (injective_design hident))

omit [DecidableEq Sample] in
private theorem sum_card_batch (batch : Sample → Batch) :
    ∑ i, (#{s | batch s = i} : ℝ) = Fintype.card Sample := by
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (f := batch) (s := Finset.univ)
    (t := Finset.univ) (by simp), Finset.card_univ]

/-- The residual sum of squares at `v` is the least one plus the squared length of the fitted
change `X (v - β̂)`, as the least-squares residual is orthogonal to the columns of `X`. -/
private theorem rss_eq_add {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) (y : m → ℝ) (v : k → ℝ) :
    ∑ s, (y s - (X *ᵥ v) s) ^ 2 = ∑ s, (y s - (X *ᵥ olsEstimator X y) s) ^ 2 +
      ∑ s, ((X *ᵥ (v - olsEstimator X y)) s) ^ 2 := by
  set c := olsEstimator X y
  have horth : (y - X *ᵥ c) ⬝ᵥ (X *ᵥ (v - c)) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose,
      MathlibExt.Probability.FiniteProbability.transpose_mulVec_sub_olsEstimator hX,
      zero_dotProduct]
  have hv : ∀ s, (X *ᵥ v) s = (X *ᵥ c) s + (X *ᵥ (v - c)) s := fun s => by
    rw [← Pi.add_apply, ← mulVec_add, add_sub_cancel]
  simp only [dotProduct, Pi.sub_apply] at horth
  have hsq : ∀ s, (y s - (X *ᵥ v) s) ^ 2 = (y s - (X *ᵥ c) s) ^ 2 + ((X *ᵥ (v - c)) s) ^ 2 -
      2 * ((y s - (X *ᵥ c) s) * (X *ᵥ (v - c)) s) := fun s => by rw [hv]; ring
  simp only [hsq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, horth]
  ring

/-- **The standardization is a constrained least-squares fit.** For one gene with expression
values `y`, ComBat's estimates `α̂`, `β̂` and `γ̃` (as in `adjust`, from the least-squares
coefficients `B` of `y` on the batch indicators and the covariates: `α̂ = ∑ i, (n i / N) B i`,
`β̂` the covariate coefficients and `γ̃ i = B i - α̂`) satisfy the constraint
`∑ i, n i * γ̃ i = 0` and minimize the residual sum of squares
`∑ s, (y s - α - ∑ k, x s k * β k - γ (batch s)) ^ 2` over all `α`, `β` and `γ`; and they are
the only minimizer that satisfies the constraint. The design is assumed identifiable: no
combination of batch effects `b` and covariate coefficients `c` vanishes on every sample unless
both are zero, which forces every batch to have a sample. -/
theorem leastSquares_standardization [Nonempty Sample] {batch : Sample → Batch}
    {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0)
    (y : Sample → ℝ) :
    let n : Batch → ℝ := fun i => #{s | batch s = i}
    let N : ℝ := Fintype.card Sample
    let B : Batch ⊕ Covariate → ℝ :=
      olsEstimator (Matrix.of fun s => Sum.elim (fun i => if batch s = i then 1 else 0) (x s)) y
    let αHat : ℝ := ∑ i, n i / N * B (.inl i)
    let βHat : Covariate → ℝ := fun k => B (.inr k)
    let γTilde : Batch → ℝ := fun i => B (.inl i) - αHat
    let rss : ℝ → (Covariate → ℝ) → (Batch → ℝ) → ℝ := fun α β γ =>
      ∑ s, (y s - α - ∑ k, x s k * β k - γ (batch s)) ^ 2
    ∑ i, n i * γTilde i = 0 ∧ (∀ α β γ, rss αHat βHat γTilde ≤ rss α β γ) ∧
      ∀ α β γ, ∑ i, n i * γ i = 0 → rss α β γ ≤ rss αHat βHat γTilde →
        α = αHat ∧ β = βHat ∧ γ = γTilde := by
  intro n N B αHat βHat γTilde rss
  have hX := isUnit_design hident
  have hN : N ≠ 0 := by simp [N, Fintype.card_ne_zero]
  have hsum : ∑ i, n i = N := sum_card_batch batch
  have hα : αHat * N = ∑ i, n i * B (.inl i) := by
    simp only [αHat, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by field_simp
  -- the residual sum of squares in matrix form
  have hrss : ∀ α β γ, rss α β γ =
      ∑ s, (y s - (design batch x *ᵥ Sum.elim (fun i => α + γ i) β) s) ^ 2 := by
    intro α β γ
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [design_mulVec]
    simp only [Sum.elim_inl, Sum.elim_inr]
    ring
  have hB : Sum.elim (fun i => αHat + γTilde i) βHat = B := by
    funext j
    rcases j with i | k
    · simp [γTilde]
    · rfl
  have hmin : rss αHat βHat γTilde =
      ∑ s, (y s - (design batch x *ᵥ olsEstimator (design batch x) y) s) ^ 2 := by
    rw [hrss, hB]
    rfl
  refine ⟨?_, fun α β γ => ?_, fun α β γ hc hle => ?_⟩
  · have : ∑ i, n i * γTilde i = ∑ i, n i * B (.inl i) - (∑ i, n i) * αHat := by
      simp only [γTilde, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [this, hsum, mul_comm, hα, sub_self]
  · rw [hmin, hrss, rss_eq_add hX y (Sum.elim (fun i => α + γ i) β)]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · rw [hmin, hrss, rss_eq_add hX y (Sum.elim (fun i => α + γ i) β)] at hle
    have hzero : ∑ s, ((design batch x *ᵥ
        (Sum.elim (fun i => α + γ i) β - olsEstimator (design batch x) y)) s) ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hzero
    have hv : Sum.elim (fun i => α + γ i) β = B := by
      refine injective_design hident ?_
      funext s
      have := hzero s (Finset.mem_univ s)
      rw [mulVec_sub, Pi.sub_apply, sq_eq_zero_iff, sub_eq_zero] at this
      exact this
    have hγ : ∀ i, α + γ i = B (.inl i) := fun i => congr_fun hv (.inl i)
    have hβ : β = βHat := funext fun k => congr_fun hv (.inr k)
    have hαeq : α = αHat := by
      have h1 : ∑ i, n i * γ i = ∑ i, n i * B (.inl i) - (∑ i, n i) * α := by
        simp only [← hγ, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
        ring
      rw [hc, hsum, ← hα] at h1
      exact mul_right_cancel₀ hN (by linarith)
    refine ⟨hαeq, hβ, funext fun i => ?_⟩
    simp only [γTilde, ← hγ, hαeq]
    ring

/-! ### Rescaling one gene -/

private theorem coef_affine {batch : Sample → Batch} {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0)
    (y : Sample → ℝ) (a b : ℝ) :
    coef batch x (fun s => a * y s + b) =
      a • coef batch x y + b • Sum.elim (fun _ => (1 : ℝ)) (fun _ => 0) := by
  have h1 : design batch x *ᵥ (b • Sum.elim (fun _ => (1 : ℝ)) (fun _ => 0)) = fun _ => b := by
    funext s
    simp [design_mulVec]
  have hy : (fun s => a * y s + b) =
      design batch x *ᵥ (b • Sum.elim (fun _ => (1 : ℝ)) (fun _ => 0)) + a • y := by
    rw [h1]
    funext s
    simp [add_comm]
  rw [coef, hy, olsEstimator_add (isUnit_design hident), mulVec_smul, add_comm]
  rfl

private theorem grand_affine [Nonempty Sample] {batch : Sample → Batch}
    {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0)
    (y : Sample → ℝ) (a b : ℝ) :
    grand batch x (fun s => a * y s + b) = a * grand batch x y + b := by
  have hN : (Fintype.card Sample : ℝ) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hsum := sum_card_batch batch
  simp only [grand, coef_affine hident, Pi.add_apply, Pi.smul_apply, Sum.elim_inl, smul_eq_mul,
    mul_one, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · rw [← Finset.sum_mul, ← Finset.sum_div, hsum, div_self hN, one_mul]

private theorem scale_affine [Nonempty Sample] {batch : Sample → Batch}
    {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0)
    (y : Sample → ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    scale batch x (fun s => a * y s + b) = a * scale batch x y := by
  simp only [scale, grand_affine hident, coef_affine hident, Pi.add_apply, Pi.smul_apply,
    Sum.elim_inl, Sum.elim_inr, smul_eq_mul, mul_one, mul_zero, add_zero]
  have : ∀ s, (a * y s + b - (a * grand batch x y + b) -
      ∑ k, x s k * (a * coef batch x y (.inr k)) -
      (a * coef batch x y (.inl (batch s)) + b - (a * grand batch x y + b))) ^ 2 =
      a ^ 2 * (y s - grand batch x y - ∑ k, x s k * coef batch x y (.inr k) -
        (coef batch x y (.inl (batch s)) - grand batch x y)) ^ 2 := fun s => by
    simp only [mul_left_comm _ a, ← Finset.mul_sum]
    ring
  simp only [this, ← Finset.mul_sum, mul_div_assoc]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

omit [Fintype Gene] in
private theorem stdz_update [DecidableEq Gene] [Nonempty Sample] {batch : Sample → Batch}
    {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0)
    (Y : Gene → Sample → ℝ) (g₀ : Gene) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    stdz batch x (Function.update Y g₀ fun s => a * Y g₀ s + b) = stdz batch x Y := by
  funext g s
  by_cases hg : g = g₀
  · subst hg
    simp only [stdz, Function.update_self, grand_affine hident, scale_affine hident _ ha,
      coef_affine hident, Pi.add_apply, Pi.smul_apply, Sum.elim_inr, smul_eq_mul, mul_zero,
      add_zero]
    rw [eq_comm, ← mul_div_mul_left _ _ ha.ne']
    congr 1
    simp only [mul_left_comm _ a, ← Finset.mul_sum]
    ring
  · simp only [stdz, Function.update_of_ne hg]

/-- **Rescaling one gene changes only its own adjustment.** Replacing the expression values of
one gene `g₀` by `a * Y g₀ s + b` with `a > 0` leaves the adjusted data of every other gene
unchanged and transforms those of `g₀` in the same way. The standardized data of `g₀` do not
change, and all the other estimates of `adjust` depend on the data only through the
standardized data. The design is assumed identifiable, as in `leastSquares_standardization`. -/
theorem adjust_update_affine [DecidableEq Gene] {batch : Sample → Batch}
    {x : Sample → Covariate → ℝ}
    (hident : ∀ (b : Batch → ℝ) (c : Covariate → ℝ),
      (∀ s, b (batch s) + ∑ k, x s k * c k = 0) → b = 0 ∧ c = 0)
    (Y : Gene → Sample → ℝ) (g₀ : Gene) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    adjust batch x (Function.update Y g₀ fun s => a * Y g₀ s + b) =
      Function.update (adjust batch x Y) g₀ fun s => a * adjust batch x Y g₀ s + b := by
  funext g s
  have : Nonempty Sample := ⟨s⟩
  rw [adjust_eq, stdz_update hident Y g₀ ha b]
  by_cases hg : g = g₀
  · subst hg
    simp only [Function.update_self, adjust_eq, grand_affine hident, scale_affine hident _ ha,
      coef_affine hident, Pi.add_apply, Pi.smul_apply, Sum.elim_inr, smul_eq_mul, mul_zero,
      add_zero]
    simp only [mul_left_comm _ a, ← Finset.mul_sum]
    ring
  · simp only [Function.update_of_ne hg, adjust_eq]

/-! ### The empirical Bayes iteration -/

/-- The sum of squares about `p` is that about the mean plus `card * (mean - p) ^ 2`. -/
private theorem sum_sq_sub_eq {ι : Type*} (t : Finset ι) (z : ι → ℝ) (p : ℝ) :
    ∑ j ∈ t, (z j - p) ^ 2 = ∑ j ∈ t, (z j - (∑ j ∈ t, z j) / t.card) ^ 2 +
      t.card * ((∑ j ∈ t, z j) / t.card - p) ^ 2 := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  have hn : (t.card : ℝ) ≠ 0 := by exact_mod_cast ht.card_pos.ne'
  set m := (∑ j ∈ t, z j) / t.card with hm
  have hsum : ∑ j ∈ t, z j = t.card * m := by rw [hm]; field_simp
  have h : ∀ j, (z j - p) ^ 2 =
      (z j - m) ^ 2 + 2 * (m - p) * z j - 2 * (m - p) * m + (m - p) ^ 2 := fun j => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hsum]
  ring

/-- The empirical Bayes iteration for one gene in one batch, with data `z j` (`j ∈ t`), prior
mean `γBar` and variance `τ2 ≥ 0` of the location, and `θ > 0`, `c > 0`, converges from any
starting value to a positive fixed point, at which the location update is continuous. The
update `next` is monotone on the positive reals and bounded there, so its orbit is monotone
from the second step on. -/
private theorem exists_tendsto_iterate {ι : Type*} (t : Finset ι) (z : ι → ℝ)
    {τ2 γBar θ c : ℝ} (hτ2 : 0 ≤ τ2) (hθ : 0 < θ) (hc : 0 < c) {post next : ℝ → ℝ}
    (hpost : ∀ d, post d =
      (t.card * τ2 * ((∑ j ∈ t, z j) / t.card) + d * γBar) / (t.card * τ2 + d))
    (hnext : ∀ d, next d = (θ + (∑ j ∈ t, (z j - post d) ^ 2) / 2) / c) (d₀ : ℝ) :
    ∃ L, 0 < L ∧ Tendsto (fun k => next^[k] d₀) atTop (𝓝 L) ∧ next L = L ∧
      ContinuousAt post L := by
  set n : ℝ := (t.card : ℝ)
  set m : ℝ := (∑ j ∈ t, z j) / t.card
  set A : ℝ := ∑ j ∈ t, (z j - m) ^ 2
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnτ : 0 ≤ n * τ2 := mul_nonneg hn hτ2
  -- the update on positive arguments, in closed form
  have hform : ∀ d, 0 < d →
      next d = (θ + (A + n * (d / (n * τ2 + d)) ^ 2 * (γBar - m) ^ 2) / 2) / c := by
    intro d hd
    have hden : n * τ2 + d ≠ 0 := by positivity
    rw [hnext, sum_sq_sub_eq t z (post d)]
    have : m - post d = -(d / (n * τ2 + d) * (γBar - m)) := by
      rw [hpost]
      field_simp
      ring
    rw [this, neg_sq, mul_pow]
    ring
  have hlow : ∀ d, θ / c ≤ next d := by
    intro d
    rw [hnext]
    gcongr
    have := Finset.sum_nonneg fun j (_ : j ∈ t) => sq_nonneg (z j - post d)
    linarith
  have hpos : ∀ d, 0 < next d := fun d => (div_pos hθ hc).trans_le (hlow d)
  have hfrac : ∀ d, 0 < d → 0 ≤ d / (n * τ2 + d) ∧ d / (n * τ2 + d) ≤ 1 := by
    intro d hd
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith
  have hup : ∀ d, 0 < d → next d ≤ (θ + (A + n * (γBar - m) ^ 2) / 2) / c := by
    intro d hd
    rw [hform d hd]
    obtain ⟨h0, h1⟩ := hfrac d hd
    have : (d / (n * τ2 + d)) ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    gcongr
    exact mul_le_of_le_one_right hn this
  have hmono : ∀ d d', 0 < d → d ≤ d' → next d ≤ next d' := by
    intro d d' hd hdd'
    have hd' : 0 < d' := hd.trans_le hdd'
    rw [hform d hd, hform d' hd']
    have h1 : d / (n * τ2 + d) ≤ d' / (n * τ2 + d') := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hdd' hnτ]
    have h2 : (d / (n * τ2 + d)) ^ 2 ≤ (d' / (n * τ2 + d')) ^ 2 :=
      pow_le_pow_left₀ (hfrac d hd).1 h1 2
    gcongr
  -- the orbit from the second step on
  set e : ℕ → ℝ := fun k => next^[k + 2] d₀ with he
  have he_succ : ∀ k, e (k + 1) = next (e k) := fun k => by
    simp only [he]
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Function.iterate_succ_apply']
  have he_eq : ∀ k, e k = next (next^[k + 1] d₀) := fun k => by
    simp only [he]
    rw [Function.iterate_succ_apply']
  have he_pos : ∀ k, 0 < e k := fun k => by rw [he_eq]; exact hpos _
  have he_low : ∀ k, θ / c ≤ e k := fun k => by rw [he_eq]; exact hlow _
  have he_up : ∀ k, e k ≤ (θ + (A + n * (γBar - m) ^ 2) / 2) / c := fun k => by
    rw [he_eq]
    refine hup _ ?_
    rw [Function.iterate_succ_apply']
    exact hpos _
  obtain ⟨L, hL⟩ : ∃ L, Tendsto e atTop (𝓝 L) := by
    rcases le_total (e 0) (e 1) with h01 | h10
    · have hmon : Monotone e := by
        refine monotone_nat_of_le_succ fun k => ?_
        induction k with
        | zero => exact h01
        | succ k ih =>
          calc e (k + 1) ≤ next (e (k + 1)) := by
                rw [he_succ k]; exact hmono _ _ (he_pos k) (by rw [← he_succ k]; exact ih)
            _ = e (k + 1 + 1) := (he_succ (k + 1)).symm
      exact ⟨_, tendsto_atTop_ciSup hmon ⟨_, by rintro _ ⟨k, rfl⟩; exact he_up k⟩⟩
    · have hanti : Antitone e := by
        refine antitone_nat_of_succ_le fun k => ?_
        induction k with
        | zero => exact h10
        | succ k ih =>
          calc e (k + 1 + 1) = next (e (k + 1)) := he_succ (k + 1)
            _ ≤ next (e k) := hmono _ _ (he_pos (k + 1)) ih
            _ = e (k + 1) := (he_succ k).symm
      exact ⟨_, tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨k, rfl⟩; exact (he_pos k).le⟩⟩
  have hL0 : 0 < L := (div_pos hθ hc).trans_le (ge_of_tendsto' hL he_low)
  have hT : Tendsto (fun k => next^[k] d₀) atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 2).mp hL
  have hpostL : ContinuousAt post L := by
    have : post = fun d => (n * τ2 * m + d * γBar) / (n * τ2 + d) := funext hpost
    rw [this]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hnextL : ContinuousAt next L := by
    have : next = fun d => (θ + (∑ j ∈ t, (z j - post d) ^ 2) / 2) / c := funext hnext
    rw [this]
    fun_prop
  exact ⟨L, hL0, hT, isFixedPt_of_tendsto_iterate hT hnextL, hpostL⟩

omit [Fintype Batch] [DecidableEq Sample] in
/-- **ComBat's empirical Bayes estimates are a joint fixed point of the conditional posterior
means.** Let `Z` be standardized data and `i` a batch with `n` samples. From the gene-wise
standardized batch means `γ̂' h` and variances `δ̂'² h` (divisor `n - 1`), the method of moments
gives the prior mean `γ̄` and variance `τ̄²` (divisor `G - 1`) of the locations and, from the mean
`V` and variance `S²` (divisor `G - 1`) of the `δ̂'² h` over the genes, the inverse-gamma
hyperparameters `λ̄ = (V² + 2 S²) / S²` and `θ̄ = (V³ + V S²) / S²`. If `S² > 0`, then `λ̄ > 2`,
`θ̄ > 0`, and `λ̄`, `θ̄` match the inverse-gamma mean `θ̄ / (λ̄ - 1) = V` and variance
`θ̄² / ((λ̄ - 1)² (λ̄ - 2)) = S²`. For each gene `g`, the iteration of `adjust` that starts at
`δ̂'² g` and alternates the two conditional posterior means
`γ = (n τ̄² γ̂' g + d γ̄) / (n τ̄² + d)` and
`d = (θ̄ + ∑ s ∈ batch i, (Z g s - γ) ^ 2 / 2) / (n / 2 + λ̄ - 1)`
converges to a limit `(γ*, δ*²)` with `δ*² > 0` that solves both equations. The estimate `γ*` is
a weighted average of `γ̂' g` and `γ̄` with weight less than `1` on `γ̂' g`: it shrinks the
gene-wise estimate towards the batch-wide mean. With `Z` the standardized data, these are the
estimates of `adjust` (`adjust_eq_of_standardized`). -/
theorem empiricalBayes_fixedPoint (batch : Sample → Batch) (Z : Gene → Sample → ℝ)
    (i : Batch) (g : Gene) :
    let n : ℝ := #{s | batch s = i}
    let G : ℝ := Fintype.card Gene
    let γHat : Gene → ℝ := fun h => (∑ s with batch s = i, Z h s) / n
    let δHat2 : Gene → ℝ := fun h => (∑ s with batch s = i, (Z h s - γHat h) ^ 2) / (n - 1)
    let γBar : ℝ := (∑ h, γHat h) / G
    let τBar2 : ℝ := (∑ h, (γHat h - γBar) ^ 2) / (G - 1)
    let V : ℝ := (∑ h, δHat2 h) / G
    let S2 : ℝ := (∑ h, (δHat2 h - V) ^ 2) / (G - 1)
    let lamBar : ℝ := (V ^ 2 + 2 * S2) / S2
    let θBar : ℝ := (V ^ 3 + V * S2) / S2
    let post : ℝ → ℝ := fun d => (n * τBar2 * γHat g + d * γBar) / (n * τBar2 + d)
    let next : ℝ → ℝ := fun d =>
      (θBar + (∑ s with batch s = i, (Z g s - post d) ^ 2) / 2) / (n / 2 + lamBar - 1)
    let δStar2 : ℝ := limUnder atTop fun k => next^[k] (δHat2 g)
    let γStar : ℝ := post δStar2
    0 < S2 →
      2 < lamBar ∧ 0 < θBar ∧ θBar / (lamBar - 1) = V ∧
      θBar ^ 2 / ((lamBar - 1) ^ 2 * (lamBar - 2)) = S2 ∧
      Tendsto (fun k => next^[k] (δHat2 g)) atTop (𝓝 δStar2) ∧
      Tendsto (fun k => post (next^[k] (δHat2 g))) atTop (𝓝 γStar) ∧ 0 < δStar2 ∧
      γStar = (n * τBar2 * γHat g + δStar2 * γBar) / (n * τBar2 + δStar2) ∧
      δStar2 = (θBar + (∑ s with batch s = i, (Z g s - γStar) ^ 2) / 2) / (n / 2 + lamBar - 1) ∧
      ∃ w, 0 ≤ w ∧ w < 1 ∧ γStar = w * γHat g + (1 - w) * γBar := by
  intro n G γHat δHat2 γBar τBar2 V S2 lamBar θBar post next δStar2 γStar hS2
  have hG : 1 ≤ Fintype.card Gene := by
    by_contra h
    have : IsEmpty Gene := Fintype.card_eq_zero_iff.mp (by omega)
    simp [S2] at hS2
  have hG1 : 0 ≤ G - 1 := by
    have : (1 : ℝ) ≤ Fintype.card Gene := by exact_mod_cast hG
    simp only [G]
    linarith
  have hGpos : 0 < G := by simp only [G]; exact_mod_cast hG
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hδ : ∀ h, 0 ≤ δHat2 h := by
    intro h
    rcases Nat.eq_zero_or_pos #{s | batch s = i} with h0 | h0
    · simp [δHat2, Finset.card_eq_zero.mp h0]
    · have : (1 : ℝ) ≤ #{s | batch s = i} := by exact_mod_cast h0
      exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by linarith)
  have hV : 0 < V := by
    have hV0 : 0 ≤ V := div_nonneg (Finset.sum_nonneg fun h _ => hδ h) hGpos.le
    refine lt_of_le_of_ne hV0 fun hV => hS2.ne' ?_
    have hsum : ∑ h, δHat2 h = 0 := by
      have h' : (∑ h, δHat2 h) / G = 0 := hV.symm
      rwa [div_eq_zero_iff, or_iff_left hGpos.ne'] at h'
    rw [Finset.sum_eq_zero_iff_of_nonneg fun h _ => hδ h] at hsum
    simp [S2, ← hV, hsum]
  have hτ : 0 ≤ τBar2 := div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hG1
  have hlam : 2 < lamBar := by
    simp only [lamBar]
    rw [lt_div_iff₀ hS2]
    nlinarith
  have hθ : 0 < θBar := div_pos (by positivity) hS2
  have hc : 0 < n / 2 + lamBar - 1 := by linarith
  obtain ⟨L, hL0, hT, hfix, hcont⟩ := exists_tendsto_iterate {s | batch s = i} (Z g) hτ hθ hc
    (post := post) (next := next) (fun d => rfl) (fun d => rfl) (δHat2 g)
  have hδL : δStar2 = L := hT.limUnder_eq
  have hlam1 : lamBar - 1 = (V ^ 2 + S2) / S2 := by
    simp only [lamBar]
    field_simp
    ring
  have hlam2 : lamBar - 2 = V ^ 2 / S2 := by
    simp only [lamBar]
    field_simp
    ring
  have hθeq : θBar = V * ((V ^ 2 + S2) / S2) := by
    simp only [θBar]
    field_simp
  have hVS : V ^ 2 + S2 ≠ 0 := by positivity
  refine ⟨hlam, hθ, ?_, ?_, hδL ▸ hT, ?_, hδL ▸ hL0, rfl, ?_, ?_⟩
  · rw [hθeq, hlam1, mul_div_assoc, div_self (div_ne_zero hVS hS2.ne'), mul_one]
  · rw [hθeq, hlam1, hlam2]
    field_simp
  · change Tendsto _ _ (𝓝 (post δStar2))
    rw [hδL]
    exact hcont.tendsto.comp hT
  · change δStar2 = next δStar2
    rw [hδL]
    exact hfix.symm
  · have hd : 0 < n * τBar2 + δStar2 := by rw [hδL]; positivity
    refine ⟨n * τBar2 / (n * τBar2 + δStar2), by positivity, ?_, ?_⟩
    · rw [div_lt_one hd]
      rw [hδL] at hd ⊢
      linarith
    · change post δStar2 = _
      simp only [post]
      field_simp
      ring

/-! ### `adjust` through its standardized data -/

/-- **ComBat's adjusted data in terms of the standardized data.** Let `α̂`, `β̂` and `σ̂` be the
standardization's estimates for `Y` (as in `adjust` and `leastSquares_standardization`), and `Z`
the standardized data, `Z h t = (Y h t - α̂ h - ∑ k, x t k * β̂ h k) / σ̂ h`. Then

  `adjust batch x Y g s = σ̂ g / √δ*² * (Z g s - γ*) + α̂ g + ∑ k, x s k * β̂ g k`,

where `δ*²` and `γ*` are the empirical Bayes estimates of `empiricalBayes_fixedPoint` for `Z`, the
batch `batch s` of the sample and the gene `g`, written with the same expressions: that theorem
describes the estimates that `adjust` uses. -/
theorem adjust_eq_of_standardized (batch : Sample → Batch) (x : Sample → Covariate → ℝ)
    (Y Z : Gene → Sample → ℝ) (g : Gene) (s : Sample) :
    let size : Batch → ℝ := fun i => #{t | batch t = i}
    let N : ℝ := Fintype.card Sample
    let B : Gene → Batch ⊕ Covariate → ℝ := fun h =>
      olsEstimator (Matrix.of fun t => Sum.elim (fun i => if batch t = i then 1 else 0) (x t)) (Y h)
    let αHat : Gene → ℝ := fun h => ∑ i, size i / N * B h (.inl i)
    let βHat : Gene → Covariate → ℝ := fun h k => B h (.inr k)
    let γTilde : Batch → Gene → ℝ := fun i h => B h (.inl i) - αHat h
    let σHat : Gene → ℝ := fun h =>
      √((∑ t, (Y h t - αHat h - ∑ k, x t k * βHat h k - γTilde (batch t) h) ^ 2) / N)
    (∀ h t, Z h t = (Y h t - αHat h - ∑ k, x t k * βHat h k) / σHat h) →
    let n : ℝ := #{t | batch t = batch s}
    let G : ℝ := Fintype.card Gene
    let γHat : Gene → ℝ := fun h => (∑ t with batch t = batch s, Z h t) / n
    let δHat2 : Gene → ℝ := fun h =>
      (∑ t with batch t = batch s, (Z h t - γHat h) ^ 2) / (n - 1)
    let γBar : ℝ := (∑ h, γHat h) / G
    let τBar2 : ℝ := (∑ h, (γHat h - γBar) ^ 2) / (G - 1)
    let V : ℝ := (∑ h, δHat2 h) / G
    let S2 : ℝ := (∑ h, (δHat2 h - V) ^ 2) / (G - 1)
    let lamBar : ℝ := (V ^ 2 + 2 * S2) / S2
    let θBar : ℝ := (V ^ 3 + V * S2) / S2
    let post : ℝ → ℝ := fun d => (n * τBar2 * γHat g + d * γBar) / (n * τBar2 + d)
    let next : ℝ → ℝ := fun d =>
      (θBar + (∑ t with batch t = batch s, (Z g t - post d) ^ 2) / 2) / (n / 2 + lamBar - 1)
    let δStar2 : ℝ := limUnder atTop fun k => next^[k] (δHat2 g)
    let γStar : ℝ := post δStar2
    adjust batch x Y g s = σHat g / √δStar2 * (Z g s - γStar) + αHat g + ∑ k, x s k * βHat g k := by
  intro size N B αHat βHat γTilde σHat hZ
  obtain rfl : Z = fun h t => (Y h t - αHat h - ∑ k, x t k * βHat h k) / σHat h :=
    funext fun h => funext fun t => hZ h t
  rfl

end Domains.Biology.Omics.ComBat
