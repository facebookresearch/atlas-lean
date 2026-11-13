/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Donor-level pseudobulk versus cell-level sampling

Single-cell experiments measure many cells from each of a few donors. The biological replicate is
the donor: cells from one donor share that donor's genotype, environment and sample handling, so
their expression values are correlated. This file makes that precise at the level of second
moments and shows three things.

1. **Cells from one donor are not independent replicates.** In the random-intercept model the
   covariance of two cells of one donor is the donor variance `σ_b²`, so for `σ_b² ≠ 0` they are
   not independent (`not_indepFun_sameDonor`). Treating them as independent understates the
   variance of the cell-level mean by the factor `1 + (m - 1) ρ` (the design effect, with
   intraclass correlation `ρ = σ_b² / (σ_b² + σ_e²)`).
2. **The per-cell variances cannot repair this.** Two random-intercept models with the same
   per-cell variance give the same variance of the cell-level mean only when their donor variances
   agree (`variance_cellMean_eq_iff`). The model with `σ_b² = 0` reproduces the naive formula
   exactly (`variance_cellMean_eq_naiveVar`). So the split of the per-cell variance into a donor and
   a residual part, an additional model, is what calibrates cell-level inference.
3. **Pseudobulk restores the replicate structure.** Averaging the `m` cells of each donor gives
   donor values that are pairwise uncorrelated with common variance `σ_b² + σ_e² / m`
   (`covariance_pseudobulk`), and the naive replicate formula applied to them is exact
   (`variance_pseudobulkMean`).

Finally, **batch perfectly confounded with condition** is a boundary case that no aggregation
fixes. The batch covariate enters the donor mean linearly; perfect confounding means it is an
affine function `batch d = a + b · cond d` of the condition with `b ≠ 0` (this covers both
`batch = cond` and `batch = 1 - cond`). Then the data have the same law under `(μ₀, τ, β)` and
`(μ₀ + a t, τ + b t, β - t)` for every a.e.-measurable noise process on a probability space
(`dataLaw_shift_of_confounded`; `dataLaw` is a probability measure, `isProbabilityMeasure_dataLaw`),
so no functional of the law of the data equals the condition effect `τ`
(`not_identifiable_of_confounded`) and no estimator is unbiased for it
(`no_unbiased_estimator_of_confounded`). The between-condition contrast estimates `τ + b β`
(`contrast_of_confounded`). One pair of donors in the same batch with different conditions
suffices to identify `τ` (`contrast_of_sameBatch`); it is not necessary, because a linear batch
covariate can also be separated from the condition across batches.

## Model

Cells are indexed by `δ × κ`: a donor `d : δ` and a cell slot `c : κ`, a balanced design with
`D = |δ|` donors and `m = |κ|` cells per donor. `Y : δ × κ → Ω → ℝ` is a family of real random
variables on a measure space `(Ω, μ)`. `IsRandomIntercept μ Y σb2 σe2` says that the variance
components are nonnegative, `σ_b² ≥ 0` and `σ_e² ≥ 0`, that every `Y i` is square integrable, and

`cov[Y (d, c), Y (d', c')] = σ_b² [d = d'] + σ_e² [(d, c) = (d', c')]` (`riCov`).

`isRandomIntercept_of_decomp` derives this from the usual decomposition
`Y (d, c) = a + b d + e (d, c)` with uncorrelated donor effects `b` of variance `σ_b²` and
residuals `e` of variance `σ_e²`, uncorrelated with `b`. `isRandomIntercept_riModel` realizes the
model for every `σ_b², σ_e² ≥ 0` on an explicit Gaussian product space (`riModel`).

## Main results

* `variance_cell`, `covariance_sameDonor`, `covariance_otherDonor`: the per-cell variance is
  `σ_b² + σ_e²`; two distinct cells of one donor have covariance `σ_b²`; cells of different donors
  are uncorrelated.
* `not_indepFun_sameDonor`: for `σ_b² ≠ 0` two distinct cells of one donor are not independent.
* `variance_cellMean`: `Var[Ȳ] = σ_b² / D + σ_e² / (D m)` (`trueVar`).
* `trueVar_sub_naiveVar`, `naiveVar_lt_trueVar`, `naiveVar_eq_trueVar_iff`: the naive
  independent-cell variance `(σ_b² + σ_e²) / (D m)` (`naiveVar`) falls short by
  `σ_b² (m - 1) / (D m)`, strictly when `σ_b² > 0` and `m ≥ 2`, and equals it exactly when
  `σ_b² = 0` or `m = 1`.
* `trueVar_eq_designEffect_mul_naiveVar`: `trueVar = (1 + (m - 1) ρ) · naiveVar`.
* `covariance_pseudobulk`, `pseudobulkMean_eq_cellMean`, `variance_pseudobulkMean`.
* `pseudoreplication_counterexample`: for every balanced design with `m ≥ 2` and every
  `σ_b² > 0`, `σ_e² ≥ 0`, the explicit Gaussian model has `Var[Ȳ] = trueVar > naiveVar`.
* `isProbabilityMeasure_dataLaw`, `dataLaw_shift_of_confounded`, `not_identifiable_of_confounded`,
  `no_unbiased_estimator_of_confounded`, `contrast_of_confounded`, `contrast_of_sameBatch`.

## Source receipt (API-00)

Reuse search (2026-11-11, base `origin/main` 53666a3c1): `MathlibExt`, `CSLibExt`, `PhyslibExt`,
`WantedExt` and Mathlib were searched for pseudobulk, pseudoreplication, design effect, intraclass
correlation, random effect and confounding. Nothing in the repository models donor/cell
replication. `MathlibExt.Biology.StatisticalGenetics.MixedModel` (`phenCov = Z G Zᵀ + R`) works
with Gaussian matrix laws and mixed-model equations; its import cone is much larger than the
scalar covariance kernel needed here, so it is not imported. Reused from Mathlib:
`ProbabilityTheory.covariance` with `covariance_fun_sum_fun_sum`, `covariance_fun_div_left/right`,
`covariance_add_left/right`, `covariance_const_add_left/right`, `covariance_self`,
`IndepFun.covariance_eq_zero` (`Mathlib.Probability.Moments.Covariance`, `.Variance`);
`iIndepFun_pi`, `measurePreserving_eval` and `gaussianReal` with `variance_id_gaussianReal`,
`memLp_id_gaussianReal` for the explicit realization.

Literature:

* S. H. Hurlbert, *Pseudoreplication and the design of ecological field experiments*,
  Ecol. Monogr. 54 (1984), 187–211 (the term and the failure mode).
* L. Kish, *Survey Sampling*, Wiley, 1965 (design effect `1 + (m - 1) ρ` for cluster samples).
* S. E. Lazic, *The problem of pseudoreplication in neuroscientific studies: is it affecting your
  analysis?*, BMC Neurosci. 11 (2010), 5.
* K. D. Zimmerman, M. A. Espeland, C. D. Langefeld, *A practical solution to pseudoreplication
  bias in single-cell studies*, Nat. Commun. 12 (2021), 738.
* J. W. Squair et al., *Confronting false discoveries in single-cell differential expression*,
  Nat. Commun. 12 (2021), 5692 (pseudobulk versus cell-level tests).
* J. T. Leek et al., *Tackling the widespread and critical impact of batch effects in
  high-throughput data*, Nat. Rev. Genet. 11 (2010), 733–739 (batch confounded with condition).

## Scope

Only second moments are modelled; the variance results need no Gaussian or independence
assumption. Unbalanced designs (donor-specific cell counts) and estimation of `σ_b²`, `σ_e²` are
not treated.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Omics.Pseudobulk

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {δ κ : Type*}

/-! ### The random-intercept covariance -/

section Defs

variable [DecidableEq δ] [DecidableEq κ]

/-- Random-intercept covariance of the cells `i = (d, c)` and `j = (d', c')`:
`σ_b² [d = d'] + σ_e² [i = j]`. -/
def riCov (σb2 σe2 : ℝ) (i j : δ × κ) : ℝ :=
  (if i.1 = j.1 then σb2 else 0) + (if i = j then σe2 else 0)

/-- The random-intercept model at the level of second moments: the donor and residual variance
components are nonnegative, every cell value is square integrable, and the cell covariances are
`riCov σb2 σe2`. The sign conditions exclude exchangeable covariances such as `Y₀ = Z`,
`Y₁ = -Z` (kernel coefficients `-1`, `2`) that no donor random effect produces. -/
structure IsRandomIntercept (μ : Measure Ω) (Y : δ × κ → Ω → ℝ) (σb2 σe2 : ℝ) : Prop where
  donorVar_nonneg : 0 ≤ σb2
  residVar_nonneg : 0 ≤ σe2
  memLp : ∀ i, MemLp (Y i) 2 μ
  cov_eq : ∀ i j, cov[Y i, Y j; μ] = riCov σb2 σe2 i j

end Defs

section Means

variable [Fintype δ] [Fintype κ]

/-- Cell-level grand mean `Ȳ = (∑ᵢ Yᵢ) / (D m)`. -/
noncomputable def cellMean (Y : δ × κ → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ (∑ i, Y i ω) / (Fintype.card δ * Fintype.card κ)

/-- Pseudobulk value of donor `d`: the mean of its `m` cells. -/
noncomputable def pseudobulk (Y : δ × κ → Ω → ℝ) (d : δ) : Ω → ℝ :=
  fun ω ↦ (∑ c, Y (d, c) ω) / Fintype.card κ

/-- Mean of the `D` pseudobulk values. -/
noncomputable def pseudobulkMean (Y : δ × κ → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ (∑ d, pseudobulk Y d ω) / Fintype.card δ

/-- Variance of the cell-level mean under the random-intercept model with `D` donors and `m`
cells per donor: `σ_b² / D + σ_e² / (D m)`. -/
noncomputable def trueVar (σb2 σe2 : ℝ) (D m : ℕ) : ℝ := σb2 / D + σe2 / (D * m)

/-- The variance of the cell-level mean that results from treating the `D m` cells as independent
replicates of per-cell variance `σ_b² + σ_e²`. -/
noncomputable def naiveVar (σb2 σe2 : ℝ) (D m : ℕ) : ℝ := (σb2 + σe2) / (D * m)

/-- Intraclass correlation `ρ = σ_b² / (σ_b² + σ_e²)`. -/
noncomputable def icc (σb2 σe2 : ℝ) : ℝ := σb2 / (σb2 + σe2)

end Means

/-! ### Covariance of averages -/

private lemma memLp_sum_div {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (a : ℝ) : MemLp (fun ω ↦ (∑ i, X i ω) / a) 2 μ := by
  have h : MemLp (fun ω ↦ ∑ i, X i ω) 2 μ := by
    convert memLp_finsetSum' (s := Finset.univ) (fun i _ ↦ hX i) using 1
    funext ω
    simp [Finset.sum_apply]
  simpa [div_eq_mul_inv] using h.mul_const a⁻¹

private lemma covariance_sum_div [IsFiniteMeasure μ] {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {X : ι → Ω → ℝ} {Z : ι' → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (hZ : ∀ j, MemLp (Z j) 2 μ)
    (a b : ℝ) :
    cov[fun ω ↦ (∑ i, X i ω) / a, fun ω ↦ (∑ j, Z j ω) / b; μ]
      = (∑ i, ∑ j, cov[X i, Z j; μ]) / (a * b) := by
  rw [covariance_fun_div_left, covariance_fun_div_right, covariance_fun_sum_fun_sum hX hZ,
    div_div, mul_comm b]

/-! ### Cells -/

section Cells

variable [DecidableEq δ] [DecidableEq κ] {Y : δ × κ → Ω → ℝ} {σb2 σe2 : ℝ}

/-- Every cell has variance `σ_b² + σ_e²`. -/
theorem variance_cell (h : IsRandomIntercept μ Y σb2 σe2) (i : δ × κ) :
    Var[Y i; μ] = σb2 + σe2 := by
  rw [← covariance_self (h.memLp i).aemeasurable, h.cov_eq]
  simp [riCov]

/-- Two distinct cells of one donor have covariance `σ_b²`. -/
theorem covariance_sameDonor (h : IsRandomIntercept μ Y σb2 σe2) (d : δ) {c c' : κ}
    (hc : c ≠ c') : cov[Y (d, c), Y (d, c'); μ] = σb2 := by
  rw [h.cov_eq]
  simp [riCov, hc]

/-- Cells of different donors are uncorrelated. -/
theorem covariance_otherDonor (h : IsRandomIntercept μ Y σb2 σe2) {d d' : δ} (hd : d ≠ d')
    (c c' : κ) : cov[Y (d, c), Y (d', c'); μ] = 0 := by
  rw [h.cov_eq]
  simp [riCov, hd]

/-- **Cells of one donor are not independent replicates**: with a nonzero donor variance, two
distinct cells of the same donor are not independent random variables. -/
theorem not_indepFun_sameDonor (h : IsRandomIntercept μ Y σb2 σe2) (hb : σb2 ≠ 0) (d : δ)
    {c c' : κ} (hc : c ≠ c') : ¬ IndepFun (Y (d, c)) (Y (d, c')) μ := fun hind ↦
  hb <| (covariance_sameDonor h d hc).symm.trans
    (hind.covariance_eq_zero (h.memLp _) (h.memLp _))

variable [Fintype δ] [Fintype κ]

/-- Row sums of the kernel: `∑ⱼ riCov i j = m σ_b² + σ_e²`. -/
theorem sum_riCov_right (i : δ × κ) :
    ∑ j, riCov σb2 σe2 i j = Fintype.card κ * σb2 + σe2 := by
  simp only [riCov, Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- **Variance of the cell-level mean**: `Var[Ȳ] = σ_b² / D + σ_e² / (D m)`. -/
theorem variance_cellMean [IsFiniteMeasure μ] [Nonempty δ] [Nonempty κ]
    (h : IsRandomIntercept μ Y σb2 σe2) :
    Var[cellMean Y; μ] = trueVar σb2 σe2 (Fintype.card δ) (Fintype.card κ) := by
  have hm := memLp_sum_div h.memLp ((Fintype.card δ : ℝ) * Fintype.card κ)
  unfold cellMean
  rw [← covariance_self hm.aemeasurable, covariance_sum_div h.memLp h.memLp]
  simp_rw [h.cov_eq, sum_riCov_right, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    nsmul_eq_mul, trueVar]
  have hD : (Fintype.card δ : ℝ) ≠ 0 := by positivity
  have hk : (Fintype.card κ : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end Cells

/-! ### Naive versus true variance -/

/-- The shortfall of the naive variance: `trueVar - naiveVar = σ_b² (m - 1) / (D m)`. -/
theorem trueVar_sub_naiveVar (σb2 σe2 : ℝ) {D m : ℕ} (hD : D ≠ 0) (hm : m ≠ 0) :
    trueVar σb2 σe2 D m - naiveVar σb2 σe2 D m = σb2 * (m - 1) / (D * m) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold trueVar naiveVar
  field_simp
  ring

/-- **Pseudoreplication understates the variance**: with a positive donor variance and at least
two cells per donor, the naive variance is strictly smaller than the true one. -/
theorem naiveVar_lt_trueVar {σb2 : ℝ} (σe2 : ℝ) (hb : 0 < σb2) {D m : ℕ} (hD : D ≠ 0)
    (hm : 2 ≤ m) : naiveVar σb2 σe2 D m < trueVar σb2 σe2 D m := by
  have hm0 : m ≠ 0 := by omega
  have key := trueVar_sub_naiveVar σb2 σe2 hD hm0
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < σb2 * (m - 1) / (D * m) := by
    have : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
    have : (0 : ℝ) < m := by linarith
    apply div_pos (mul_pos hb (by linarith)) (by positivity)
  linarith

/-- The naive variance is exact precisely when there is no donor variance or one cell per
donor. -/
theorem naiveVar_eq_trueVar_iff (σb2 σe2 : ℝ) {D m : ℕ} (hD : D ≠ 0) (hm : m ≠ 0) :
    naiveVar σb2 σe2 D m = trueVar σb2 σe2 D m ↔ σb2 = 0 ∨ m = 1 := by
  have key := trueVar_sub_naiveVar σb2 σe2 hD hm
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  constructor
  · intro heq
    rw [heq, sub_self, eq_comm, div_eq_zero_iff, mul_eq_zero, mul_eq_zero, sub_eq_zero] at key
    rcases key with (hb | h1) | (h | h)
    · exact Or.inl hb
    · exact Or.inr (by exact_mod_cast h1)
    · exact absurd h hD'
    · exact absurd h hm'
  · rintro (hb | h1)
    · rw [hb] at key ⊢
      linarith [show (0 : ℝ) * (m - 1) / (D * m) = 0 by simp]
    · subst h1
      have : σb2 * ((1 : ℕ) - 1 : ℝ) / (D * (1 : ℕ)) = 0 := by simp
      linarith

/-- **Design effect**: `trueVar = (1 + (m - 1) ρ) · naiveVar` with `ρ = icc σ_b² σ_e²`, whenever
the per-cell variance `σ_b² + σ_e²` is nonzero. -/
theorem trueVar_eq_designEffect_mul_naiveVar {σb2 σe2 : ℝ} (hs : σb2 + σe2 ≠ 0) {D m : ℕ}
    (hD : D ≠ 0) (hm : m ≠ 0) :
    trueVar σb2 σe2 D m = (1 + (m - 1) * icc σb2 σe2) * naiveVar σb2 σe2 D m := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold trueVar naiveVar icc
  field_simp
  ring

/-! ### The per-cell variances do not determine the variance of the mean -/

section PerCellVariance

variable [Fintype δ] [Fintype κ] [DecidableEq δ] [DecidableEq κ]
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsFiniteMeasure μ]
  [IsFiniteMeasure μ']

/-- **The independence model reproduces the naive formula**: a random-intercept model with no
donor variance and per-cell variance `σ_b² + σ_e²` has cell-mean variance exactly `naiveVar`. -/
theorem variance_cellMean_eq_naiveVar [Nonempty δ] [Nonempty κ] {Y : δ × κ → Ω → ℝ} {σb2 σe2 : ℝ}
    (h : IsRandomIntercept μ Y 0 (σb2 + σe2)) :
    Var[cellMean Y; μ] = naiveVar σb2 σe2 (Fintype.card δ) (Fintype.card κ) := by
  rw [variance_cellMean h, trueVar, naiveVar, zero_div, zero_add]

/-- **Same per-cell variance, different precision**: two random-intercept models on possibly
different spaces whose cells have the same variance give the same variance of the cell-level mean
only if their donor variances agree, as soon as there are two cells per donor. Within the
random-intercept family the per-cell variance therefore cannot calibrate cell-level inference
without a model of the donor split. -/
theorem variance_cellMean_eq_iff [Nonempty δ] (hm : 2 ≤ Fintype.card κ) {Y : δ × κ → Ω → ℝ}
    {Y' : δ × κ → Ω' → ℝ} {σb2 σe2 σb2' σe2' : ℝ} (h : IsRandomIntercept μ Y σb2 σe2)
    (h' : IsRandomIntercept μ' Y' σb2' σe2') (hs : σb2 + σe2 = σb2' + σe2') :
    Var[cellMean Y; μ] = Var[cellMean Y'; μ'] ↔ σb2 = σb2' := by
  have : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  rw [variance_cellMean h, variance_cellMean h']
  have hD : (Fintype.card δ : ℝ) ≠ 0 := by positivity
  have hm1 : (1 : ℝ) < Fintype.card κ := by exact_mod_cast hm
  have hk : (Fintype.card κ : ℝ) ≠ 0 := by positivity
  have he : σe2' = σb2 + σe2 - σb2' := by linarith
  subst he
  unfold trueVar
  constructor
  · intro heq
    field_simp at heq
    have : (σb2 - σb2') * ((Fintype.card κ : ℝ) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith
  · rintro rfl
    ring_nf

end PerCellVariance

/-! ### Pseudobulk -/

section Pseudobulk

variable [Fintype δ] [Fintype κ] {Y : δ × κ → Ω → ℝ} {σb2 σe2 : ℝ}

omit [Fintype δ] in
theorem memLp_pseudobulk [DecidableEq δ] [DecidableEq κ] (h : IsRandomIntercept μ Y σb2 σe2)
    (d : δ) :
    MemLp (pseudobulk Y d) 2 μ :=
  memLp_sum_div (fun c ↦ h.memLp (d, c)) _

omit [Fintype δ] in
/-- **Pseudobulk values are uncorrelated replicates**: distinct donors' pseudobulk values are
uncorrelated, and each has variance `σ_b² + σ_e² / m`. -/
theorem covariance_pseudobulk [DecidableEq δ] [DecidableEq κ] [IsFiniteMeasure μ] [Nonempty κ]
    (h : IsRandomIntercept μ Y σb2 σe2) (d d' : δ) :
    cov[pseudobulk Y d, pseudobulk Y d'; μ]
      = if d = d' then σb2 + σe2 / Fintype.card κ else 0 := by
  unfold pseudobulk
  rw [covariance_sum_div (fun c ↦ h.memLp (d, c))
    (fun c ↦ h.memLp (d', c))]
  simp_rw [h.cov_eq, riCov, Prod.mk.injEq]
  have hk : (Fintype.card κ : ℝ) ≠ 0 := by positivity
  split_ifs with hd
  · subst hd
    simp only [true_and, ↓reduceIte, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ]
    field_simp
  · simp [hd]

omit [Fintype δ] in
theorem variance_pseudobulk [DecidableEq δ] [DecidableEq κ] [IsFiniteMeasure μ] [Nonempty κ]
    (h : IsRandomIntercept μ Y σb2 σe2) (d : δ) :
    Var[pseudobulk Y d; μ] = σb2 + σe2 / Fintype.card κ := by
  rw [← covariance_self (memLp_pseudobulk h d).aemeasurable, covariance_pseudobulk h]
  simp

/-- In a balanced design the mean of the pseudobulk values is the cell-level mean. -/
theorem pseudobulkMean_eq_cellMean [Nonempty κ] (Y : δ × κ → Ω → ℝ) :
    pseudobulkMean Y = cellMean Y := by
  funext ω
  have hk : (Fintype.card κ : ℝ) ≠ 0 := by positivity
  simp only [pseudobulkMean, pseudobulk, cellMean, ← Finset.sum_div, Fintype.sum_prod_type]
  rw [div_div, mul_comm (Fintype.card κ : ℝ)]

/-- **The replicate formula is exact for pseudobulk**: the variance of the mean of the `D`
pseudobulk values is `Var[pseudobulk] / D`, which equals the true variance of the cell-level
mean. -/
theorem variance_pseudobulkMean [DecidableEq δ] [DecidableEq κ] [IsFiniteMeasure μ] [Nonempty δ]
    [Nonempty κ] (h : IsRandomIntercept μ Y σb2 σe2) :
    Var[pseudobulkMean Y; μ] = (σb2 + σe2 / Fintype.card κ) / Fintype.card δ ∧
      Var[pseudobulkMean Y; μ] = trueVar σb2 σe2 (Fintype.card δ) (Fintype.card κ) := by
  have h1 : Var[pseudobulkMean Y; μ] = (σb2 + σe2 / Fintype.card κ) / Fintype.card δ := by
    have hm := memLp_sum_div (memLp_pseudobulk h) (Fintype.card δ : ℝ)
    unfold pseudobulkMean
    rw [← covariance_self hm.aemeasurable,
      covariance_sum_div (memLp_pseudobulk h) (memLp_pseudobulk h)]
    simp_rw [covariance_pseudobulk h, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hD : (Fintype.card δ : ℝ) ≠ 0 := by positivity
    field_simp
  refine ⟨h1, ?_⟩
  rw [h1, trueVar]
  have hD : (Fintype.card δ : ℝ) ≠ 0 := by positivity
  have hk : (Fintype.card κ : ℝ) ≠ 0 := by positivity
  field_simp

end Pseudobulk

/-! ### The decomposition `Y = a + b + e` and an explicit realization -/

section Realization

variable [DecidableEq δ] [DecidableEq κ]

/-- **Donor random effect plus residual**: if `Y (d, c) = a + b d + e (d, c)` with pairwise
uncorrelated donor effects of variance `σ_b² ≥ 0`, pairwise uncorrelated residuals of variance
`σ_e² ≥ 0`, and `b` uncorrelated with `e`, then `Y` is a random-intercept model. -/
theorem isRandomIntercept_of_decomp [IsProbabilityMeasure μ] {σb2 σe2 : ℝ} (hσb : 0 ≤ σb2)
    (hσe : 0 ≤ σe2) (a : ℝ) {b : δ → Ω → ℝ} {e : δ × κ → Ω → ℝ} (hb : ∀ d, MemLp (b d) 2 μ)
    (he : ∀ i, MemLp (e i) 2 μ)
    (hbb : ∀ d d', cov[b d, b d'; μ] = if d = d' then σb2 else 0)
    (hee : ∀ i j, cov[e i, e j; μ] = if i = j then σe2 else 0)
    (hbe : ∀ d j, cov[b d, e j; μ] = 0) :
    IsRandomIntercept μ (fun i ω ↦ a + (b i.1 ω + e i ω)) σb2 σe2 where
  donorVar_nonneg := hσb
  residVar_nonneg := hσe
  memLp i := (memLp_const a).add ((hb i.1).add (he i))
  cov_eq i j := by
    have hYi : MemLp (fun ω ↦ b i.1 ω + e i ω) 2 μ := (hb i.1).add (he i)
    have hYj : MemLp (fun ω ↦ b j.1 ω + e j ω) 2 μ := (hb j.1).add (he j)
    rw [covariance_const_add_left (hYi.integrable one_le_two) a,
      covariance_const_add_right (hYj.integrable one_le_two) a]
    have hl : cov[fun ω ↦ b i.1 ω + e i ω, fun ω ↦ b j.1 ω + e j ω; μ]
        = cov[b i.1, b j.1; μ] + cov[e i, b j.1; μ] + (cov[b i.1, e j; μ] + cov[e i, e j; μ]) := by
      rw [show (fun ω ↦ b i.1 ω + e i ω) = b i.1 + e i from rfl,
        show (fun ω ↦ b j.1 ω + e j ω) = b j.1 + e j from rfl,
        covariance_add_left (hb _) (he _) ((hb _).add (he _)),
        covariance_add_right (hb _) (hb _) (he _), covariance_add_right (he _) (hb _) (he _)]
      ring
    rw [hl, hbb, hee, covariance_comm, hbe, hbe, riCov]
    ring

/-- Sample space of the explicit realization: one coordinate per donor effect and one per cell
residual. -/
abbrev NoiseSpace (δ κ : Type*) : Type _ := δ ⊕ δ × κ → ℝ

/-- Independent standard Gaussian coordinates on `NoiseSpace δ κ`. -/
noncomputable def stdGaussianPi (δ κ : Type*) [Fintype δ] [Fintype κ] :
    Measure (NoiseSpace δ κ) :=
  Measure.pi fun _ ↦ gaussianReal 0 1

instance [Fintype δ] [Fintype κ] : IsProbabilityMeasure (stdGaussianPi δ κ) := by
  unfold stdGaussianPi; infer_instance

/-- **Explicit random-intercept model**: `Y (d, c) = √σ_b² Z_d + √σ_e² W_{d c}` with independent
standard Gaussians `Z_d`, `W_{d c}`. -/
noncomputable def riModel (σb2 σe2 : ℝ) : δ × κ → NoiseSpace δ κ → ℝ :=
  fun i ω ↦ 0 + (Real.sqrt σb2 * ω (Sum.inl i.1) + Real.sqrt σe2 * ω (Sum.inr i))

omit [DecidableEq δ] [DecidableEq κ] in
private lemma memLp_coord [Fintype δ] [Fintype κ] (a : δ ⊕ δ × κ) :
    MemLp (fun ω : NoiseSpace δ κ ↦ ω a) 2 (stdGaussianPi δ κ) :=
  (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ a)

omit [DecidableEq δ] [DecidableEq κ] in
private lemma covariance_coord [Fintype δ] [Fintype κ] [DecidableEq (δ ⊕ δ × κ)]
    (a a' : δ ⊕ δ × κ) :
    cov[fun ω : NoiseSpace δ κ ↦ ω a, fun ω ↦ ω a'; stdGaussianPi δ κ]
      = if a = a' then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [covariance_self (memLp_coord a).aemeasurable]
    have := (measurePreserving_eval (fun _ : δ ⊕ δ × κ ↦ gaussianReal 0 1) a).variance_fun_comp
      (f := id) aemeasurable_id
    simpa [stdGaussianPi, variance_id_gaussianReal] using this
  · have hind := (iIndepFun_pi (μ := fun _ : δ ⊕ δ × κ ↦ gaussianReal 0 1) (X := fun _ ↦ id)
      (fun _ ↦ aemeasurable_id)).indepFun h
    exact hind.covariance_eq_zero (memLp_coord a) (memLp_coord a')

/-- The explicit Gaussian model is a random-intercept model for every `σ_b², σ_e² ≥ 0`. -/
theorem isRandomIntercept_riModel [Fintype δ] [Fintype κ] {σb2 σe2 : ℝ} (hb : 0 ≤ σb2)
    (he : 0 ≤ σe2) :
    IsRandomIntercept (stdGaussianPi δ κ) (riModel σb2 σe2) σb2 σe2 := by
  classical
  refine isRandomIntercept_of_decomp
    (b := fun d (ω : NoiseSpace δ κ) ↦ Real.sqrt σb2 * ω (Sum.inl d))
    (e := fun i (ω : NoiseSpace δ κ) ↦ Real.sqrt σe2 * ω (Sum.inr i)) hb he 0
    (fun d ↦ (memLp_coord _).const_mul _) (fun i ↦ (memLp_coord _).const_mul _) ?_ ?_ ?_
  · intro d d'
    rw [covariance_const_mul_left, covariance_const_mul_right, covariance_coord]
    simp only [Sum.inl.injEq]
    split_ifs <;> simp [Real.mul_self_sqrt hb]
  · intro i j
    rw [covariance_const_mul_left, covariance_const_mul_right, covariance_coord]
    simp only [Sum.inr.injEq]
    split_ifs <;> simp [Real.mul_self_sqrt he]
  · intro d j
    rw [covariance_const_mul_left, covariance_const_mul_right, covariance_coord]
    simp

/-- **Pseudoreplication counterexample**: in every balanced design with at least two cells per
donor and every donor variance `σ_b² > 0`, the explicit Gaussian random-intercept model has
cell-mean variance `σ_b² / D + σ_e² / (D m)`, strictly above the naive independent-cell value
`(σ_b² + σ_e²) / (D m)`. -/
theorem pseudoreplication_counterexample [Fintype δ] [Fintype κ] [Nonempty δ]
    (hm : 2 ≤ Fintype.card κ) {σb2 σe2 : ℝ} (hb : 0 < σb2) (he : 0 ≤ σe2) :
    IsRandomIntercept (stdGaussianPi δ κ) (riModel σb2 σe2) σb2 σe2 ∧
      Var[cellMean (riModel σb2 σe2 : δ × κ → _ → ℝ); stdGaussianPi δ κ]
        = trueVar σb2 σe2 (Fintype.card δ) (Fintype.card κ) ∧
      naiveVar σb2 σe2 (Fintype.card δ) (Fintype.card κ)
        < Var[cellMean (riModel σb2 σe2 : δ × κ → _ → ℝ); stdGaussianPi δ κ] := by
  have : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  have h := isRandomIntercept_riModel (δ := δ) (κ := κ) hb.le he
  have hv := variance_cellMean h
  exact ⟨h, hv, hv ▸ naiveVar_lt_trueVar σe2 hb Fintype.card_ne_zero hm⟩

end Realization

/-! ### Batch perfectly confounded with condition -/

section Confounding

variable (cond batch : δ → ℝ)

/-- Donor-level mean `μ₀ + τ · cond d + β · batch d`: intercept `μ₀`, condition effect `τ`, batch
effect `β`. -/
def meanFn (μ₀ τ β : ℝ) (d : δ) : ℝ := μ₀ + τ * cond d + β * batch d

/-- Observed cell values: the donor mean plus a noise process `U` (for instance a random-intercept
model). -/
def obs (μ₀ τ β : ℝ) (U : δ × κ → Ω → ℝ) (i : δ × κ) (ω : Ω) : ℝ :=
  meanFn cond batch μ₀ τ β i.1 + U i ω

/-- Law of the whole cell-level data vector. It is defined only for a probability measure `μ` and
a noise process that is a.e.-measurable as a vector-valued map `Ω → (δ × κ → ℝ)`; then the
observation map is a.e.-measurable (`aemeasurable_obs`) and the push-forward is a probability
measure (`isProbabilityMeasure_dataLaw`), not the zero fallback of `Measure.map`. -/
noncomputable def dataLaw (μ : Measure Ω) [IsProbabilityMeasure μ] (μ₀ τ β : ℝ)
    (U : δ × κ → Ω → ℝ) (_hU : AEMeasurable (fun ω i ↦ U i ω) μ) : Measure (δ × κ → ℝ) :=
  μ.map fun ω i ↦ obs cond batch μ₀ τ β U i ω

variable {cond batch}

/-- The observation vector is a.e.-measurable whenever the noise vector is. -/
theorem aemeasurable_obs {U : δ × κ → Ω → ℝ} (hU : AEMeasurable (fun ω i ↦ U i ω) μ)
    (μ₀ τ β : ℝ) : AEMeasurable (fun ω i ↦ obs cond batch μ₀ τ β U i ω) μ :=
  hU.const_add (fun i ↦ meanFn cond batch μ₀ τ β i.1)

/-- The data law is a probability measure. -/
instance isProbabilityMeasure_dataLaw [IsProbabilityMeasure μ] {U : δ × κ → Ω → ℝ}
    (hU : AEMeasurable (fun ω i ↦ U i ω) μ) (μ₀ τ β : ℝ) :
    IsProbabilityMeasure (dataLaw cond batch μ μ₀ τ β U hU) := by
  unfold dataLaw
  exact (Measure.isProbabilityMeasure_map_iff (aemeasurable_obs hU μ₀ τ β)).2 inferInstance

/-- Under perfect confounding, `batch = a + b · cond`, the observations are unchanged when batch
effect is traded for condition effect and intercept. -/
theorem obs_shift_of_confounded {a b : ℝ} (hcb : batch = fun d ↦ a + b * cond d)
    (μ₀ τ β t : ℝ) (U : δ × κ → Ω → ℝ) :
    obs cond batch (μ₀ + a * t) (τ + b * t) (β - t) U = obs cond batch μ₀ τ β U := by
  subst hcb
  funext i ω
  simp only [obs, meanFn]
  ring

/-- **Perfect confounding, full law**: if `batch = a + b · cond`, then for every a.e.-measurable
noise process on a probability space the data have the same law under `(μ₀, τ, β)` and
`(μ₀ + a t, τ + b t, β - t)`. -/
theorem dataLaw_shift_of_confounded {a b : ℝ} (hcb : batch = fun d ↦ a + b * cond d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (μ₀ τ β t : ℝ) (U : δ × κ → Ω → ℝ)
    (hU : AEMeasurable (fun ω i ↦ U i ω) μ) :
    dataLaw cond batch μ (μ₀ + a * t) (τ + b * t) (β - t) U hU
      = dataLaw cond batch μ μ₀ τ β U hU := by
  simp only [dataLaw, obs_shift_of_confounded hcb]

/-- **The condition effect is not identifiable** under perfect confounding
(`batch = a + b · cond`, `b ≠ 0`): no functional of the law of the cell-level data recovers `τ`,
whatever the a.e.-measurable noise process. Pseudobulk values, being functions of the data, do
not help. -/
theorem not_identifiable_of_confounded {a b : ℝ} (hcb : batch = fun d ↦ a + b * cond d)
    (hb : b ≠ 0) (μ : Measure Ω) [IsProbabilityMeasure μ] (U : δ × κ → Ω → ℝ)
    (hU : AEMeasurable (fun ω i ↦ U i ω) μ) :
    ¬ ∃ F : Measure (δ × κ → ℝ) → ℝ, ∀ μ₀ τ β, F (dataLaw cond batch μ μ₀ τ β U hU) = τ := by
  rintro ⟨F, hF⟩
  have hs := dataLaw_shift_of_confounded hcb μ 0 0 1 1 U hU
  simp only [zero_add, mul_one, sub_self] at hs
  have h1 := hF a b 0
  rw [hs, hF] at h1
  exact hb h1.symm

/-- **No unbiased estimator** of `τ` exists under perfect confounding (`batch = a + b · cond`,
`b ≠ 0`): any estimator `T` of the cell-level data has the same expectation under `(0, 0, 1)` and
`(a, b, 0)`. -/
theorem no_unbiased_estimator_of_confounded {a b : ℝ} (hcb : batch = fun d ↦ a + b * cond d)
    (hb : b ≠ 0) (μ : Measure Ω) (U : δ × κ → Ω → ℝ) :
    ¬ ∃ T : (δ × κ → ℝ) → ℝ,
      ∀ μ₀ τ β, ∫ ω, T (fun i ↦ obs cond batch μ₀ τ β U i ω) ∂μ = τ := by
  rintro ⟨T, hT⟩
  have hs := obs_shift_of_confounded hcb 0 0 1 1 U
  simp only [zero_add, mul_one, sub_self] at hs
  have h1 := hT a b 0
  rw [hs, hT] at h1
  exact hb h1.symm

section Contrast

variable [IsProbabilityMeasure μ] {U : δ × κ → Ω → ℝ}

private lemma integral_obs (hU : ∀ i, Integrable (U i) μ) (hU0 : ∀ i, ∫ ω, U i ω ∂μ = 0)
    (μ₀ τ β : ℝ) (i : δ × κ) :
    ∫ ω, obs cond batch μ₀ τ β U i ω ∂μ = meanFn cond batch μ₀ τ β i.1 := by
  simp only [obs]
  rw [integral_add (integrable_const _) (hU i), integral_const, hU0]
  simp

/-- **What the contrast estimates under confounding**: if `batch = a + b · cond`, then with
mean-zero noise the difference in expected cell values between a donor with `cond = 1` and one
with `cond = 0` is `τ + b β`. -/
theorem contrast_of_confounded {a b : ℝ} (hcb : batch = fun d ↦ a + b * cond d)
    (hU : ∀ i, Integrable (U i) μ) (hU0 : ∀ i, ∫ ω, U i ω ∂μ = 0) {d₀ d₁ : δ} (h₀ : cond d₀ = 0)
    (h₁ : cond d₁ = 1)
    (μ₀ τ β : ℝ) (c₀ c₁ : κ) :
    ∫ ω, obs cond batch μ₀ τ β U (d₁, c₁) ω ∂μ - ∫ ω, obs cond batch μ₀ τ β U (d₀, c₀) ω ∂μ
      = τ + b * β := by
  subst hcb
  rw [integral_obs hU hU0, integral_obs hU hU0]
  simp only [meanFn, h₀, h₁]
  ring

/-- **Identification away from the boundary**: one pair of donors in the same batch whose
condition indicators differ by one identifies `τ` from the mean-zero-noise expectations. Under
perfect confounding (`batch = a + b · cond`, `b ≠ 0`) no such pair exists. Such a pair is
sufficient, not necessary: the batch covariate enters linearly, so for `batch = ![0, 1, 2]` and
`cond = ![0, 1, 1]` no two donors share a batch, yet `(m₁ - m₀) - (m₂ - m₁) = τ` for the donor
means `mᵢ`. -/
theorem contrast_of_sameBatch (hU : ∀ i, Integrable (U i) μ) (hU0 : ∀ i, ∫ ω, U i ω ∂μ = 0)
    {d₀ d₁ : δ} (hb : batch d₀ = batch d₁) (hc : cond d₁ = cond d₀ + 1) (μ₀ τ β : ℝ)
    (c₀ c₁ : κ) :
    ∫ ω, obs cond batch μ₀ τ β U (d₁, c₁) ω ∂μ - ∫ ω, obs cond batch μ₀ τ β U (d₀, c₀) ω ∂μ
      = τ := by
  rw [integral_obs hU hU0, integral_obs hU hU0]
  simp only [meanFn, hc, hb]
  ring

end Contrast

end Confounding

end MathlibExt.Biology.Omics.Pseudobulk
