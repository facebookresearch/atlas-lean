/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import MathlibExt.Probability.Distributions.NegativeBinomialMeasure
public import MathlibExt.Probability.Statistics.GLM.NegativeBinomial
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Negative-binomial test for allele-specific reporter activity

Morova et al. (2023), Materials and Methods, "Testing bi-allelic activity".

In a massively parallel reporter assay, a library of DNA fragments, each carrying a known allele
of a candidate variant and a barcode, is transfected into cells; the activity of a fragment is
read as its RNA barcode count relative to its abundance in the plasmid pool. At one biallelic SNP
the fragments that overlap it, `i : ι`, are distinct barcoded plasmids. Fragment `i` carries the
alternative allele (`Xᵢ = 1`) or the reference allele (`Xᵢ = 0`), has plasmid DNA read count
`Pᵢ ≥ 1` and RNA read count `Yᵢ`.

The negative-binomial regression with logarithmic link and offset `log Pᵢ` makes the RNA counts
independent, `Yᵢ ~ NB(θ, μᵢ)` with a size `θ > 0` common to the fragments of the SNP and mean

`log μᵢ = β₀ + β₁ Xᵢ + log Pᵢ`,

so that `β₀` is the log expression per plasmid of the reference allele and `β₁` the log fold change
of expression per plasmid between the alternative and the reference allele. Allele-specific
activity is the test of `H₀ : β₁ = 0` against `H₁ : β₁ ≠ 0`, with `β₀` and `θ` free, made only at
SNPs with more than `15` distinct plasmids carrying each allele.

The test is stated by its hypotheses. No test statistic, p-value or calibration is fixed here: the
source fits the regression by maximum likelihood, `θ` included, and calibrates the type I error
empirically on fragments that carry no tested variant.

## Main definitions

* `Design`: the allele carried by, and the plasmid count of, each fragment at a SNP;
  `Design.IsTested`: more than `15` distinct plasmids carry each allele.
* `Parameters`: the coefficients `β₀`, `β₁` and the size `θ > 0`.
* `Design.mean`: `μᵢ = exp (β₀ + β₁ Xᵢ + log Pᵢ)`; `Design.fragmentLaw`: the law `NB(θ, μᵢ)` of
  `Yᵢ`; `Design.countLaw`: the law of the RNA counts, the product of the fragment laws.
* `allelicActivityTest`: the test at a tested SNP, as the pair of the sets of laws of the RNA
  counts that `H₀ : β₁ = 0` and `H₁ : β₁ ≠ 0` allow.

## Main results

* `Design.log_integral_countLaw`: `log E(Yᵢ) = β₀ + β₁ Xᵢ + log Pᵢ`.
* `Design.log_mean_div_plasmidCount_of_ref`, `Design.log_mean_div_plasmidCount_of_alt`,
  `Design.log_foldChange`: `β₀` is the log expression per plasmid of the reference allele and `β₁`
  the log fold change of expression per plasmid.
* `Design.countLaw_real_singleton`: the likelihood of the RNA counts is `∏ᵢ NB(Yᵢ; θ, μᵢ)`;
  `Design.log_countLaw_real_singleton`: its logarithm is a term free of `(β₀, β₁)` plus the
  negative binomial regression log-likelihood `nbLogLik` with design rows `(1, Xᵢ)` and offsets
  `log Pᵢ`.
* `Design.countLaw_eq_of_β₁_eq_zero`: under `H₀` the law of the RNA counts does not depend on
  which allele each fragment carries.
* `Design.β₁_eq_of_countLaw_eq`: when both alleles are present, the law of the RNA counts
  determines `β₁`. Hence the two hypotheses of `allelicActivityTest` are disjoint
  (`disjoint_allelicActivityTest`), together make up the model
  (`union_allelicActivityTest`), and a law of the model satisfies `H₀` exactly when its
  `β₁ = 0` (`countLaw_mem_allelicActivityTest_fst_iff`).

## References

* T. Morova, Y. Ding, C.-F. Huang, F. Sar, T. Schwarz, C. Giambartolomei et al., *Optimized
  high-throughput screening of non-coding variants identified from genome-wide association
  studies*, Nucleic Acids Res. 51 (2023), e18, Materials and Methods ("Testing bi-allelic
  activity").
-/

@[expose] public section

set_option autoImplicit false

namespace Domains.Biology.Omics.AlleleSpecificReporter

open MeasureTheory ProbabilityTheory Real Finset Matrix
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial (nbLogLik log_negBinomialReal_exp)
open scoped Nat

/-- **Reporter data at one SNP.** The fragments `i : ι` that overlap a biallelic SNP are distinct
barcoded plasmids of the library. Fragment `i` carries the alternative allele when
`carriesAlt i = true` and the reference allele when `carriesAlt i = false`, and its barcode has
plasmid DNA read count `plasmidCount i`. The plasmid counts are positive, so that the offsets
`log Pᵢ` are defined. -/
structure Design (ι : Type*) where
  /-- Whether fragment `i` carries the alternative allele (`Xᵢ = 1`) rather than the reference
  allele (`Xᵢ = 0`). -/
  carriesAlt : ι → Bool
  /-- The plasmid DNA read count `Pᵢ` of the barcode of fragment `i`. -/
  plasmidCount : ι → ℕ
  plasmidCount_pos : ∀ i, 0 < plasmidCount i

/-- **Parameters of the regression at one SNP**: the intercept `β₀`, the allelic effect `β₁` and
the size `θ > 0` of the negative binomial law of the RNA counts, common to the fragments of the
SNP. -/
structure Parameters where
  /-- The intercept `β₀`: the log expression per plasmid of the reference allele. -/
  β₀ : ℝ
  /-- The allelic effect `β₁`: the log fold change of expression per plasmid between the
  alternative and the reference allele. -/
  β₁ : ℝ
  /-- The size (shape) `θ` of the negative binomial law of the RNA counts. -/
  θ : ℝ
  θ_pos : 0 < θ

/-- The coefficient vector `(β₀, β₁)` of the regression. -/
def Parameters.coef (p : Parameters) : Fin 2 → ℝ := ![p.β₀, p.β₁]

namespace Design

variable {ι : Type*} (D : Design ι)

/-- **Which SNPs are tested**: those with more than `15` distinct plasmids carrying the
alternative allele and more than `15` carrying the reference allele. -/
def IsTested [Fintype ι] : Prop :=
  15 < #{i | D.carriesAlt i = true} ∧ 15 < #{i | D.carriesAlt i = false}

instance [Fintype ι] : Decidable D.IsTested := by
  unfold IsTested
  infer_instance

/-- The allele indicator `Xᵢ ∈ {0, 1}`: `1` if fragment `i` carries the alternative allele and `0`
if it carries the reference allele. -/
def alleleIndicator (i : ι) : ℝ := if D.carriesAlt i then 1 else 0

/-- The offset `log Pᵢ` of fragment `i`, the logarithm of its plasmid count. -/
noncomputable def offset (i : ι) : ℝ := log (D.plasmidCount i)

/-- The mean RNA count of fragment `i` under the logarithmic link,
`μᵢ = exp (β₀ + β₁ Xᵢ + log Pᵢ)`. -/
noncomputable def mean (p : Parameters) (i : ι) : ℝ :=
  exp (p.β₀ + p.β₁ * D.alleleIndicator i + D.offset i)

/-- The law of the RNA count of fragment `i`: negative binomial with the size `θ` and the mean
`μᵢ` of the regression. -/
noncomputable def fragmentLaw (p : Parameters) (i : ι) : Measure ℕ :=
  negBinomialMeasure p.θ (D.mean p i)

instance (p : Parameters) (i : ι) : IsProbabilityMeasure (D.fragmentLaw p i) :=
  isProbabilityMeasure_negBinomialMeasure p.θ_pos (exp_pos _).le

/-- **The negative-binomial regression model** of the RNA counts at one SNP: the RNA counts `Yᵢ`
of the fragments are independent, with `Yᵢ ~ NB(θ, μᵢ)` and `log μᵢ = β₀ + β₁ Xᵢ + log Pᵢ`. -/
noncomputable def countLaw [Fintype ι] (p : Parameters) : Measure (ι → ℕ) :=
  Measure.pi (D.fragmentLaw p)

instance [Fintype ι] (p : Parameters) : IsProbabilityMeasure (D.countLaw p) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

/-! ### The mean and its parametrization -/

theorem mean_pos (p : Parameters) (i : ι) : 0 < D.mean p i := exp_pos _

/-- **Logarithmic link with offset**: `log μᵢ = β₀ + β₁ Xᵢ + log Pᵢ`. -/
theorem log_mean (p : Parameters) (i : ι) :
    log (D.mean p i) = p.β₀ + p.β₁ * D.alleleIndicator i + log (D.plasmidCount i) := by
  rw [mean, log_exp, offset]

/-- The expression per plasmid of fragment `i` is `μᵢ / Pᵢ = exp (β₀ + β₁ Xᵢ)`. -/
theorem mean_div_plasmidCount (p : Parameters) (i : ι) :
    D.mean p i / D.plasmidCount i = exp (p.β₀ + p.β₁ * D.alleleIndicator i) := by
  have hP : (0 : ℝ) < D.plasmidCount i := Nat.cast_pos.2 (D.plasmidCount_pos i)
  rw [mean, offset, exp_add, exp_log hP, mul_div_cancel_right₀ _ hP.ne']

/-- **`β₀` is the log expression per plasmid of the reference allele**: for a fragment carrying
the reference allele, `log (μᵢ / Pᵢ) = β₀`. -/
theorem log_mean_div_plasmidCount_of_ref (p : Parameters) {i : ι}
    (hi : D.carriesAlt i = false) : log (D.mean p i / D.plasmidCount i) = p.β₀ := by
  rw [mean_div_plasmidCount, log_exp, alleleIndicator, hi]
  simp

/-- For a fragment carrying the alternative allele, `log (μᵢ / Pᵢ) = β₀ + β₁`. -/
theorem log_mean_div_plasmidCount_of_alt (p : Parameters) {i : ι}
    (hi : D.carriesAlt i = true) : log (D.mean p i / D.plasmidCount i) = p.β₀ + p.β₁ := by
  rw [mean_div_plasmidCount, log_exp, alleleIndicator, hi]
  simp

/-- **`β₁` is the log fold change of expression per plasmid** between a fragment `i` carrying the
alternative allele and a fragment `j` carrying the reference allele:
`log ((μᵢ / Pᵢ) / (μⱼ / Pⱼ)) = β₁`. -/
theorem log_foldChange (p : Parameters) {i j : ι} (hi : D.carriesAlt i = true)
    (hj : D.carriesAlt j = false) :
    log (D.mean p i / D.plasmidCount i / (D.mean p j / D.plasmidCount j)) = p.β₁ := by
  rw [mean_div_plasmidCount, mean_div_plasmidCount, ← exp_sub, log_exp, alleleIndicator,
    alleleIndicator, hi, hj]
  simp

/-! ### The law of the RNA counts -/

/-- **The mean RNA count.** Under the model the RNA count `Yᵢ` of fragment `i` has mean `μᵢ`. -/
theorem integral_countLaw [Fintype ι] (p : Parameters) (i : ι) :
    ∫ y, (y i : ℝ) ∂D.countLaw p = D.mean p i :=
  (integral_comp_eval (μ := D.fragmentLaw p) (i := i) (f := fun k : ℕ => (k : ℝ))
    Measurable.of_discrete.aestronglyMeasurable).trans
    (integral_negBinomialMeasure p.θ_pos (D.mean_pos p i).le)

/-- **The regression equation** `log E(Yᵢ) = β₀ + β₁ Xᵢ + log Pᵢ`: the negative-binomial regression
of the RNA counts with logarithmic link and offset `log Pᵢ`. -/
theorem log_integral_countLaw [Fintype ι] (p : Parameters) (i : ι) :
    log (∫ y, (y i : ℝ) ∂D.countLaw p) =
      p.β₀ + p.β₁ * D.alleleIndicator i + log (D.plasmidCount i) := by
  rw [integral_countLaw, log_mean]

/-- **Likelihood.** The probability of the RNA counts `y` is `∏ᵢ NB(yᵢ; θ, μᵢ)`. -/
theorem countLaw_real_singleton [Fintype ι] (p : Parameters) (y : ι → ℕ) :
    (D.countLaw p).real {y} = ∏ i, negBinomialReal p.θ (D.mean p i) (y i) := by
  rw [countLaw, measureReal_def, ← Set.univ_pi_singleton y, Measure.pi_pi, ENNReal.toReal_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [← measureReal_def]
  exact negBinomialMeasure_real_singleton p.θ_pos (D.mean_pos p i).le (y i)

/-- The design matrix of the regression: row `i` is `(1, Xᵢ)`, an intercept and the allele
indicator. -/
noncomputable def designMatrix : Matrix ι (Fin 2) ℝ :=
  Matrix.of fun i => ![1, D.alleleIndicator i]

theorem designMatrix_mulVec (p : Parameters) (i : ι) :
    (D.designMatrix *ᵥ p.coef) i = p.β₀ + p.β₁ * D.alleleIndicator i := by
  simp [designMatrix, Parameters.coef, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- **The log-likelihood is a negative binomial regression log-likelihood.** The logarithm of the
probability of the RNA counts `y` is a term free of `(β₀, β₁)` plus `nbLogLik θ X o y (β₀, β₁)`,
the negative binomial regression log-likelihood with logarithmic link, design rows `(1, Xᵢ)`,
offsets `oᵢ = log Pᵢ` and size `θ`. -/
theorem log_countLaw_real_singleton [Fintype ι] (p : Parameters) (y : ι → ℕ) :
    log ((D.countLaw p).real {y}) =
      ∑ i, (log ((ascPochhammer ℝ (y i)).eval p.θ / (y i)!) + p.θ * log p.θ) +
        nbLogLik p.θ D.designMatrix D.offset (fun i => (y i : ℝ)) p.coef := by
  rw [countLaw_real_singleton,
    log_prod fun i _ => (negBinomialReal_pos p.θ_pos (D.mean_pos p i) (y i)).ne']
  simp only [nbLogLik, designMatrix_mulVec, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mean, log_negBinomialReal_exp p.θ_pos]

/-! ### The hypotheses -/

/-- **Under `H₀` the allele does not matter.** With `β₁ = 0`, two designs that differ only in
which allele each fragment carries give the RNA counts the same law. -/
theorem countLaw_eq_of_β₁_eq_zero [Fintype ι] (D' : Design ι)
    (h : D.plasmidCount = D'.plasmidCount) {p : Parameters} (hp : p.β₁ = 0) :
    D.countLaw p = D'.countLaw p := by
  rw [countLaw, countLaw]
  congr 1
  funext i
  simp only [fragmentLaw, mean, offset, hp, h, zero_mul]

/-- The law of the RNA counts determines the mean RNA count of every fragment. -/
theorem mean_eq_of_countLaw_eq [Fintype ι] {p q : Parameters} (h : D.countLaw p = D.countLaw q)
    (i : ι) : D.mean p i = D.mean q i := by
  rw [← integral_countLaw, h, integral_countLaw]

/-- **Identifiability of the allelic effect.** If a fragment `i` carries the alternative allele and
a fragment `j` the reference allele, the law of the RNA counts determines `β₁`. -/
theorem β₁_eq_of_countLaw_eq [Fintype ι] {p q : Parameters} {i j : ι}
    (hi : D.carriesAlt i = true) (hj : D.carriesAlt j = false)
    (h : D.countLaw p = D.countLaw q) : p.β₁ = q.β₁ := by
  have hi' := congrArg log (D.mean_eq_of_countLaw_eq h i)
  have hj' := congrArg log (D.mean_eq_of_countLaw_eq h j)
  simp [log_mean, alleleIndicator, hi, hj] at hi' hj'
  linarith

/-- At a tested SNP some fragment carries the alternative allele. -/
theorem IsTested.exists_alt [Fintype ι] {D : Design ι} (hD : D.IsTested) :
    ∃ i, D.carriesAlt i = true := by
  obtain ⟨i, hi⟩ := card_pos.1 (lt_of_le_of_lt (Nat.zero_le 15) hD.1)
  exact ⟨i, (mem_filter.1 hi).2⟩

/-- At a tested SNP some fragment carries the reference allele. -/
theorem IsTested.exists_ref [Fintype ι] {D : Design ι} (hD : D.IsTested) :
    ∃ j, D.carriesAlt j = false := by
  obtain ⟨j, hj⟩ := card_pos.1 (lt_of_le_of_lt (Nat.zero_le 15) hD.2)
  exact ⟨j, (mem_filter.1 hj).2⟩

end Design

/-- **Negative-binomial test for allele-specific reporter activity** (Morova et al. 2023). At a
SNP with reporter data `D` that is tested, with more than `15` distinct plasmids carrying each
allele, allele-specific activity is the test of `H₀ : β₁ = 0` against `H₁ : β₁ ≠ 0` in the
negative-binomial regression `Design.countLaw` of `D`, with logarithmic link and offset `log Pᵢ`:
the RNA counts `Yᵢ` are independent, `Yᵢ ~ NB(θ, μᵢ)` with a common size `θ > 0` and
`log E(Yᵢ) = β₀ + β₁ Xᵢ + log Pᵢ`, where `β₀` is the log expression per plasmid of the reference
allele and `β₁` the log fold change of expression per plasmid between the alternative and the
reference allele. The test is the pair `(H₀, H₁)` of the sets of laws of the RNA counts that the
two hypotheses allow, `β₀` and `θ` being free in both. -/
noncomputable def allelicActivityTest {ι : Type*} [Fintype ι] (D : {D : Design ι // D.IsTested}) :
    Set (Measure (ι → ℕ)) × Set (Measure (ι → ℕ)) :=
  (D.1.countLaw '' {p | p.β₁ = 0}, D.1.countLaw '' {p | p.β₁ ≠ 0})

section Test

variable {ι : Type*} [Fintype ι] (D : {D : Design ι // D.IsTested})

/-- **A law of the model satisfies `H₀` exactly when its allelic effect is `0`.** -/
theorem countLaw_mem_allelicActivityTest_fst_iff (p : Parameters) :
    D.1.countLaw p ∈ (allelicActivityTest D).1 ↔ p.β₁ = 0 := by
  obtain ⟨i, hi⟩ := D.2.exists_alt
  obtain ⟨j, hj⟩ := D.2.exists_ref
  constructor
  · rintro ⟨q, hq, h⟩
    rw [← D.1.β₁_eq_of_countLaw_eq hi hj h]
    exact hq
  · exact fun hp => ⟨p, hp, rfl⟩

/-- **A law of the model satisfies `H₁` exactly when its allelic effect is not `0`.** -/
theorem countLaw_mem_allelicActivityTest_snd_iff (p : Parameters) :
    D.1.countLaw p ∈ (allelicActivityTest D).2 ↔ p.β₁ ≠ 0 := by
  obtain ⟨i, hi⟩ := D.2.exists_alt
  obtain ⟨j, hj⟩ := D.2.exists_ref
  constructor
  · rintro ⟨q, hq, h⟩
    rw [← D.1.β₁_eq_of_countLaw_eq hi hj h]
    exact hq
  · exact fun hp => ⟨p, hp, rfl⟩

/-- **The two hypotheses are disjoint**: no law of the RNA counts is allowed by both. -/
theorem disjoint_allelicActivityTest :
    Disjoint (allelicActivityTest D).1 (allelicActivityTest D).2 := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ h
  exact (countLaw_mem_allelicActivityTest_snd_iff D p).1 h hp

/-- **Together the two hypotheses make up the model**: every law of the negative-binomial
regression is allowed by `H₀` or by `H₁`. -/
theorem union_allelicActivityTest :
    (allelicActivityTest D).1 ∪ (allelicActivityTest D).2 = Set.range D.1.countLaw := by
  rw [allelicActivityTest, ← Set.image_union, ← Set.image_univ]
  congr 1
  ext p
  simpa using em (p.β₁ = 0)

end Test

end Domains.Biology.Omics.AlleleSpecificReporter
