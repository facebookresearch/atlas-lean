/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.HardyWeinberg
public import CSLibExt.MachineLearning.Bayesian.Basic
public import MathlibExt.Probability.Statistics.LinearModel.CoefficientT
public import MathlibExt.Probability.FiniteProbability
public import Mathlib.Probability.ConditionalProbability

/-!
# B-allele-frequency regression estimator of contamination

A genotyping array reports, at each biallelic marker with alleles labelled `A` and `B`, a called
genotype and the B allele frequency (BAF), an estimate of the abundance of allele `B` computed
from the normalized probe intensities, close to `0`, `1/2` and `1` for `AA`, `AB` and `BB` in a
clean sample. Jun et al. (2012) estimate the fraction `α` of a DNA sample that comes from an
unrelated contaminant from the BAF at markers called homozygous.

**Convention.** As in the source, the genotype call at a marker is taken to be the target's
genotype in the array's `A`/`B` labels: calls are assumed correct, and every conditional mean and
posterior below conditions on the target's genotype itself. A call made from the intensities of a
contaminated sample can differ from it (by `baf_eq`, an `AA` target with a `BB` contaminant at
`α = 3/10` has modelled BAF `3/10`), and the statements below say nothing about such calls.

Alleles are `Bool`, with `false` the allele `A` and `true` the allele `B`. A genotype is an
ordered pair `g : Bool × Bool` of a maternal and a paternal allele, as in
`MathlibExt.Biology.PopulationGenetics.HardyWeinberg`, whose two-allele lemmas use the opposite
label (`true` is the allele `A` there).

**Modelled BAF.** The module models the BAF without noise or calibration. When intensity is
linear in DNA input and a fraction `α` of the DNA comes from a contaminant of genotype `g₂`,
`baf α g₁ g₂` is the share `I_B / (I_A + I_B)` of the `B` probe in the intensities of a target of
genotype `g₁`, which is `(1 - α) n(g₁) / 2 + α n(g₂) / 2`, where `n(g)` is the number of copies of
`B` in `g` (`baf_eq`). The array's BAF is a calibrated estimate, not this share, and the
regression below treats the observed BAF `y` as the modelled mean plus an error. The conditional
means below are those of the modelled BAF.

**Parameter ranges.** The contamination fraction `α` lies in `[0, 1]`, but the formulas hold for
every real `α`; outside `[0, 1]`, `baf` is only the value of the formula: for an `AA` target and a
`BB` contaminant it is `α`, so `2` at `α = 2`, which is no allele frequency. Likewise, in the
minor-allele model `gamete G true` is the frequency of the allele coded `true` for every `G`, and
is the minor allele frequency only when it is at most `1/2`; the statements hold for every `G`.

**Conditional means.** If the contaminant's two alleles are drawn independently of the target's
genotype, and of each other, from the population allele frequencies `p_A, p_B` (`markerLaw`), then,
whatever the law of the target's genotype, for each homozygous class to which that law assigns
positive probability

* `E[BAF | g = AA] = α p_B` (`integral_baf_cond_homA`) and
* `E[BAF | g = BB] = 1 - α p_A` (`integral_baf_cond_homB`).

Both are the linear mean `γ + α p + τ 1(g = AA)` with `γ = 1`, `τ = -1` and the signed frequency
`p = p_B` at `AA`, `p = -p_A` at `BB` (`integral_baf_cond_homozygous`).

**Regression estimator.** Over `n` homozygous markers, Equation 4 of the source fits the observed
BAF as `y = γ + α p + τ 1(g = AA) + ε` by least squares. `contaminationEstimate` is the
least-squares slope `α̂`, the `α` coordinate of the ordinary least-squares estimate for the design
matrix with rows `(1, p, 1(g = AA))` (`designMatrix`), and `contaminationTStatistic` is the `t`
statistic of `α = 0`, the coefficient `t` statistic of the slope. For a full-rank design, `α̂`
recovers `α` from noiseless data (`contaminationEstimate_mulVec`), in particular from the
conditional means above (`contaminationEstimate_integral_baf_cond`), and is unbiased under mean-zero
errors (`integral_contaminationEstimate`). Under `α = 0` with i.i.d. Gaussian errors and `n > 3`,
the `t` statistic has Student's `t` law with `n - 3` degrees of freedom
(`hasLaw_contaminationTStatistic`), so the one-sided test that rejects `α = 0` in favour of `α > 0`
when it exceeds `t₀` has level `P(t_{n-3} > t₀)` (`measureReal_lt_contaminationTStatistic`).

**Minor-allele covariate.** When only the minor allele frequency `f` is known, suppose the label `B`
sits on the minor allele with probability `1/2`, independently of the genotypes, and the target's
genotype follows Hardy–Weinberg proportions. Alleles are then coded `true` for the minor allele and
`false` for the major one, the population has genotype law `G` with minor allele frequency
`f = gamete G true` (see Parameter ranges), and the orientation `θ` (`true`: `B` is the minor
allele) relabels them (`toAB`). Write `g` for the target's genotype in `A`/`B` labels. Then
`g = AA` has probability `(1 - f)²` when `B` is the minor allele and `f²` otherwise
(`callLikelihood_true_homA`, `callLikelihood_false_homA`), so by Bayes' rule the posterior
probability that `B` is the minor allele given `g = AA` is `(1 - f)² / ((1 - f)² + f²)`
(`posterior_callLikelihood_homA`), and

* `E[BAF | g = AA] = α f (1 - f) / ((1 - f)² + f²)` (`integral_baf_cond_minorAllele`).

## Main definitions

* `baf`: the modelled, noiseless BAF of a contaminated sample, from the probe intensities
  `intensityA`, `intensityB`.
* `markerLaw`: the joint law of the target's and the contaminant's genotypes, the contaminant's
  with independent alleles of law `p` (`iidGenotype` of
  `MathlibExt.Biology.PopulationGenetics.HardyWeinberg`).
* `designMatrix`, `contaminationEstimate`, `contaminationTStatistic`: the regression of Equation 4.
* `toAB`, `minorAlleleLaw`, `callLikelihood`: the minor-allele model.

## References

* G. Jun, M. Flickinger, K. N. Hetrick et al., *Detecting and estimating contamination of human
  DNA samples in sequencing and array-based genotype data*, American Journal of Human Genetics 91
  (2012), 839–848, Material and Methods, "Regression-Based Method" (Equation 4 and the
  minor-allele calculation following it).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Biology.PopulationGenetics.HardyWeinberg
open MathlibExt.Probability.Statistics.LinearModel
open Cslib.MachineLearning.Bayesian
open MathlibExt.Probability.FiniteProbability (sum_toReal_eq_one)
open scoped ENNReal

namespace Domains.Biology.StatisticalGenetics.BAFContamination

/-! ### The B allele frequency of a contaminated sample -/

/-- The number of copies of allele `B` (`true`) in a genotype `g`: `0` for `AA`, `1` for a
heterozygote and `2` for `BB`. -/
def countB (g : Bool × Bool) : ℕ := g.1.toNat + g.2.toNat

/-- The `B`-probe intensity of a sample in which a fraction `α` of the DNA comes from a
contaminant of genotype `g₂` and the rest from the target of genotype `g₁`, when intensity is
linear in DNA input: `(1 - α) n(g₁) + α n(g₂)` with `n(g)` the number of copies of `B` in `g`,
in units of the intensity of one copy at full DNA input. -/
def intensityB (α : ℝ) (g₁ g₂ : Bool × Bool) : ℝ :=
  (1 - α) * countB g₁ + α * countB g₂

/-- The `A`-probe intensity of the same sample: `(1 - α) (2 - n(g₁)) + α (2 - n(g₂))`, as each
genotype carries `2 - n(g)` copies of `A`. -/
def intensityA (α : ℝ) (g₁ g₂ : Bool × Bool) : ℝ :=
  (1 - α) * (2 - countB g₁ : ℝ) + α * (2 - countB g₂ : ℝ)

/-- The modelled, noiseless B allele frequency (BAF) of a sample in which a fraction `α` of the DNA
comes from a contaminant of genotype `g₂` and the rest from the target of genotype `g₁`: the share
`I_B / (I_A + I_B)` of the `B` probe in intensities linear in DNA input. The BAF an array reports
is a calibrated estimate of the abundance of `B`, which the regression of Equation 4 treats as
such a mean plus an error. The fraction `α` lies in `[0, 1]`; for other real `α` this is only the
value of the formula. -/
noncomputable def baf (α : ℝ) (g₁ g₂ : Bool × Bool) : ℝ :=
  intensityB α g₁ g₂ / (intensityA α g₁ g₂ + intensityB α g₁ g₂)

/-- **The modelled BAF of a contaminated sample** is the mixture `(1 - α) n(g₁) / 2 + α n(g₂) / 2`
of the shares of allele `B` in the target's genotype `g₁` and the contaminant's genotype `g₂`; for
a clean sample (`α = 0`) it is `0`, `1/2` and `1` for `AA`, a heterozygote and `BB`. -/
theorem baf_eq (α : ℝ) (g₁ g₂ : Bool × Bool) :
    baf α g₁ g₂ = (1 - α) * (countB g₁ / 2) + α * (countB g₂ / 2) := by
  have h : intensityA α g₁ g₂ + intensityB α g₁ g₂ = 2 := by
    simp only [intensityA, intensityB]
    ring
  rw [baf, h, intensityB]
  ring

/-! ### Conditional means at homozygous markers -/

/-- The pair of a draw from `μ` and an independent draw from `ν` has mass `μ a * ν b` at
`(a, b)`. -/
private theorem bind_map_prodMk_apply {α β : Type*} (μ : PMF α) (ν : PMF β) (a : α) (b : β) :
    (μ.bind fun x => ν.map (Prod.mk x)) (a, b) = μ a * ν b := by
  classical
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro c hc
      simp [Ne.symm hc]
  · intro c hc
    rw [PMF.map_apply]
    simp [Ne.symm hc]

/-- The joint law of the target's genotype `g₁` and the contaminant's genotype `g₂` at a marker:
`g₁` has law `T`, and the contaminant's two alleles are drawn independently of `g₁`, and of each
other, from the population allele frequencies `p`. -/
noncomputable def markerLaw (T : PMF (Bool × Bool)) (p : PMF Bool) :
    PMF ((Bool × Bool) × (Bool × Bool)) :=
  T.bind fun g₁ => (iidGenotype p).map (Prod.mk g₁)

/-- Under `markerLaw T p` the two genotypes are independent with laws `T` and `iidGenotype p`. -/
theorem markerLaw_apply (T : PMF (Bool × Bool)) (p : PMF Bool)
    (x : (Bool × Bool) × (Bool × Bool)) :
    markerLaw T p x = T x.1 * iidGenotype p x.2 :=
  bind_map_prodMk_apply T (iidGenotype p) x.1 x.2

/-- The mean of `f` under a probability mass function on a finite type, conditioned on an
event `s`: the `s`-part of the sum `∑ μ x f x`, divided by the mass of `s`. -/
private theorem integral_cond_toMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : PMF Ω) (s : Set Ω) [DecidablePred (· ∈ s)] (f : Ω → ℝ) :
    ∫ x, f x ∂(μ.toMeasure[|s]) =
      (∑ x, if x ∈ s then (μ x).toReal * f x else 0) /
        ∑ x, if x ∈ s then (μ x).toReal else 0 := by
  have hs : MeasurableSet s := s.toFinite.measurableSet
  rw [integral_fintype .of_finite]
  have hden : (μ.toMeasure s).toReal = ∑ x, if x ∈ s then (μ x).toReal else 0 := by
    rw [μ.toMeasure_apply_fintype, ENNReal.toReal_sum fun x _ => ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h : x ∈ s <;> simp [h]
    · by_cases h : x ∈ s <;> simp [h, μ.apply_ne_top]
  have hx : ∀ x, (μ.toMeasure[|s]).real {x} =
      (μ.toMeasure s).toReal⁻¹ * if x ∈ s then (μ x).toReal else 0 := by
    intro x
    rw [Measure.real, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
    congr 1
    by_cases h : x ∈ s
    · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h),
        μ.toMeasure_apply_singleton x (measurableSet_singleton x)]
      simp [h]
    · rw [Set.inter_singleton_eq_empty.mpr h]
      simp [h]
  simp_rw [hx, smul_eq_mul, hden]
  rw [div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

/-- The two allele frequencies of a biallelic marker sum to one: `p_A + p_B = 1`. -/
private theorem toReal_false_add_toReal_true (p : PMF Bool) :
    (p false).toReal + (p true).toReal = 1 := by
  simpa [Fintype.sum_bool, add_comm] using sum_toReal_eq_one p

/-- The mean share of allele `B` in a genotype with independent alleles of law `p` is `p_B`. -/
private theorem sum_iidGenotype_mul_countB (p : PMF Bool) :
    ∑ g, (iidGenotype p g).toReal * ((countB g : ℝ) / 2) = (p true).toReal := by
  have h := toReal_false_add_toReal_true p
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, iidGenotype_apply, ENNReal.toReal_mul,
    countB, Bool.toNat_true, Bool.toNat_false]
  push_cast
  linear_combination (p true).toReal * h

/-- Conditioning `markerLaw T p` on the target's genotype `g` leaves the contaminant's genotype
with its law `iidGenotype p`. -/
private theorem integral_cond_markerLaw (T : PMF (Bool × Bool)) (p : PMF Bool)
    {g : Bool × Bool} (hg : T g ≠ 0) (h : (Bool × Bool) × (Bool × Bool) → ℝ) :
    ∫ x, h x ∂((markerLaw T p).toMeasure[|Prod.fst ⁻¹' {g}]) =
      ∑ g₂, (iidGenotype p g₂).toReal * h (g, g₂) := by
  classical
  have hT : (T g).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hg, T.apply_ne_top g⟩
  have hsum : ∀ F : (Bool × Bool) → (Bool × Bool) → ℝ,
      (∑ x, ∑ y, if x = g then F x y else 0) = ∑ y, F g y := by
    intro F
    rw [Fintype.sum_eq_single g fun x hx => by simp [hx]]
    simp
  rw [integral_cond_toMeasure]
  simp only [Set.mem_preimage, Set.mem_singleton_iff,
    Fintype.sum_prod_type (α₁ := Bool × Bool) (α₂ := Bool × Bool), markerLaw_apply,
    ENNReal.toReal_mul]
  rw [hsum, hsum]
  simp_rw [mul_assoc, ← Finset.mul_sum, sum_toReal_eq_one (iidGenotype p), mul_one]
  rw [mul_div_cancel_left₀ _ hT]

/-- **Conditional mean of the modelled BAF at `AA` markers** (Jun et al. 2012): if the
contaminant's two alleles are drawn independently of the target's genotype from the population
allele frequencies `p`, then at a marker where the target is `AA`, `E[BAF | g = AA] = α p_B` for
the modelled BAF `baf`, whatever the law `T` of the target's genotype (which must give `AA`
positive probability). -/
theorem integral_baf_cond_homA (α : ℝ) (T : PMF (Bool × Bool)) (p : PMF Bool)
    (hT : T (false, false) ≠ 0) :
    ∫ x, baf α x.1 x.2 ∂((markerLaw T p).toMeasure[|Prod.fst ⁻¹' {(false, false)}]) =
      α * (p true).toReal := by
  rw [integral_cond_markerLaw T p hT]
  have key : ∀ g₂, (iidGenotype p g₂).toReal * baf α (false, false) g₂ =
      α * ((iidGenotype p g₂).toReal * ((countB g₂ : ℝ) / 2)) := by
    intro g₂
    rw [baf_eq]
    simp only [countB, Bool.toNat_false]
    push_cast
    ring
  simp_rw [key, ← Finset.mul_sum, sum_iidGenotype_mul_countB]

/-- **Conditional mean of the modelled BAF at `BB` markers** (Jun et al. 2012): if the
contaminant's two alleles are drawn independently of the target's genotype from the population
allele frequencies `p`, then at a marker where the target is `BB`, `E[BAF | g = BB] = 1 - α p_A`
for the modelled BAF `baf`, whatever the law `T` of the target's genotype (which must give `BB`
positive probability). -/
theorem integral_baf_cond_homB (α : ℝ) (T : PMF (Bool × Bool)) (p : PMF Bool)
    (hT : T (true, true) ≠ 0) :
    ∫ x, baf α x.1 x.2 ∂((markerLaw T p).toMeasure[|Prod.fst ⁻¹' {(true, true)}]) =
      1 - α * (p false).toReal := by
  rw [integral_cond_markerLaw T p hT]
  have key : ∀ g₂, (iidGenotype p g₂).toReal * baf α (true, true) g₂ =
      (1 - α) * (iidGenotype p g₂).toReal +
        α * ((iidGenotype p g₂).toReal * ((countB g₂ : ℝ) / 2)) := by
    intro g₂
    rw [baf_eq]
    simp only [countB, Bool.toNat_true]
    push_cast
    ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, sum_toReal_eq_one (iidGenotype p),
    sum_iidGenotype_mul_countB]
  linear_combination α * toReal_false_add_toReal_true p

/-! ### The regression of Equation 4 -/

/-- The signed population frequency `p` of the regression at a marker where the target is
homozygous for allele `c` (`false`: `AA`, `true`: `BB`), given the population frequency `p_B` of
`B`: `p = p_B` at `AA` and `p = -p_A = -(1 - p_B)` at `BB`. -/
def signedFreq (c : Bool) (pB : ℝ) : ℝ := if c then -(1 - pB) else pB

/-- The indicator `1(g = AA)` of a marker where the target is homozygous for allele `c`. -/
def indicatorAA (c : Bool) : ℝ := if c then 0 else 1

/-- The regressors `(1, p, 1(g = AA))` of the intercept `γ`, the slope `α` and the genotype
offset `τ` at a marker where the target is homozygous for allele `c`, with `p` the signed
frequency `signedFreq c pB`. -/
def designRow (c : Bool) (pB : ℝ) : Fin 3 → ℝ := ![1, signedFreq c pB, indicatorAA c]

/-- **The homozygous conditional means are linear in the signed frequency**: under `markerLaw T p`
the conditional mean of the modelled BAF at a marker where the target is homozygous for allele `c`,
for a target law `T` that assigns that homozygous class positive probability, is
`γ + α p + τ 1(g = AA)` with `γ = 1`, `τ = -1` and the signed frequency `p` of `c`, so stacking
the `AA` and `BB` markers gives the same slope `α` in both classes. -/
theorem integral_baf_cond_homozygous (α : ℝ) (T : PMF (Bool × Bool)) (p : PMF Bool) (c : Bool)
    (hT : T (c, c) ≠ 0) :
    ∫ x, baf α x.1 x.2 ∂((markerLaw T p).toMeasure[|Prod.fst ⁻¹' {(c, c)}]) =
      designRow c (p true).toReal ⬝ᵥ ![1, α, -1] := by
  cases c
  · rw [integral_baf_cond_homA α T p hT]
    simp [designRow, signedFreq, indicatorAA, dotProduct, Fin.sum_univ_three]
    ring
  · rw [integral_baf_cond_homB α T p hT]
    simp [designRow, signedFreq, indicatorAA, dotProduct, Fin.sum_univ_three]
    linear_combination (-α) * toReal_false_add_toReal_true p

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The design matrix of Equation 4 over the homozygous markers `i : ι`, with row
`(1, p_i, 1(g_i = AA))`: the target is homozygous for allele `c i` (`false`: `AA`, `true`: `BB`)
at marker `i`, where `B` has population frequency `pB i`. -/
def designMatrix (c : ι → Bool) (pB : ι → ℝ) : Matrix ι (Fin 3) ℝ :=
  Matrix.of fun i => designRow (c i) (pB i)

/-- **The B-allele-frequency regression estimator of contamination** (Jun et al. 2012,
Equation 4). Over homozygous markers `i : ι`, where the target is homozygous for allele `c i`
(`false`: `AA`, `true`: `BB`), `B` has population frequency `pB i` and the observed BAF, the
array's estimate, is `y i`, fit `y = γ + α p + τ 1(g = AA) + ε` by least squares, with
`p = p_B` at `AA` and `p = -p_A` at `BB`. The estimate `α̂` of the contamination level is the
least-squares slope, the coordinate of `α` in the ordinary least-squares estimate `(Xᵀ X)⁻¹ Xᵀ y`
for the design matrix `X` with rows `(1, p_i, 1(g_i = AA))`. It is meaningful for a full-rank
design (`Xᵀ X` invertible, which needs both homozygous classes and some spread of `p` within one
of them); for a singular `Xᵀ X`, whose Mathlib inverse is `0`, it is `0`. -/
noncomputable def contaminationEstimate (c : ι → Bool) (pB y : ι → ℝ) : ℝ :=
  olsEstimator (designMatrix c pB) y 1

/-- The `t` statistic of the null hypothesis `α = 0` in the regression of Equation 4: the
least-squares slope `α̂` divided by its estimated standard error `√((‖y - X β̂‖² / (n - 3)) · v)`,
where `n` is the number of markers and `v` is the diagonal entry of `(Xᵀ X)⁻¹` at the slope; the
coefficient `t` statistic of the slope at the value `0`. The one-sided test of `α = 0` against
`α > 0` rejects for large values. -/
noncomputable def contaminationTStatistic (c : ι → Bool) (pB y : ι → ℝ) : ℝ :=
  coefficientTStatistic (designMatrix c pB) 1 0 y

/-- **The regression recovers `α` from noiseless data**: for a full-rank design, if every BAF lies
on the regression line `γ + α p + τ 1(g = AA)`, as the conditional means do
(`integral_baf_cond_homozygous`), the least-squares slope is `α`. -/
theorem contaminationEstimate_mulVec (c : ι → Bool) (pB : ι → ℝ)
    (hX : IsUnit ((designMatrix c pB)ᵀ * designMatrix c pB)) (γ α τ : ℝ) :
    contaminationEstimate c pB (designMatrix c pB *ᵥ ![γ, α, τ]) = α := by
  have h := olsEstimator_add hX ![γ, α, τ] 0
  rw [add_zero, mulVec_zero, add_zero] at h
  rw [contaminationEstimate, h]
  rfl

/-- **The regression of the conditional means recovers the contamination level**: if at each
homozygous marker `i` the target's genotype has a law `T i` that assigns the marker's homozygous
class positive probability, the contaminant's alleles are drawn from the allele frequencies `p i`
(`markerLaw`), and the response at each marker is the conditional mean of the modelled BAF given
the target's genotype, then for a full-rank design the least-squares slope `α̂` of Equation 4 is
exactly `α`. -/
theorem contaminationEstimate_integral_baf_cond (α : ℝ) (c : ι → Bool)
    (T : ι → PMF (Bool × Bool)) (p : ι → PMF Bool) (hT : ∀ i, T i (c i, c i) ≠ 0)
    (hX : IsUnit ((designMatrix c fun i => (p i true).toReal)ᵀ *
      designMatrix c fun i => (p i true).toReal)) :
    contaminationEstimate c (fun i => (p i true).toReal) (fun i =>
      ∫ x, baf α x.1 x.2 ∂((markerLaw (T i) (p i)).toMeasure[|Prod.fst ⁻¹' {(c i, c i)}])) =
      α := by
  have h : (fun i =>
      ∫ x, baf α x.1 x.2 ∂((markerLaw (T i) (p i)).toMeasure[|Prod.fst ⁻¹' {(c i, c i)}])) =
      designMatrix c (fun i => (p i true).toReal) *ᵥ ![1, α, -1] := by
    funext i
    rw [integral_baf_cond_homozygous α (T i) (p i) (c i) (hT i)]
    rfl
  rw [h, contaminationEstimate_mulVec _ _ hX]

/-- **Unbiasedness of the regression estimator**: for a full-rank design and integrable errors of
mean zero, the least-squares slope of `BAF = γ + α p + τ 1(g = AA) + ε` has expectation `α`. -/
theorem integral_contaminationEstimate {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (c : ι → Bool) (pB : ι → ℝ)
    (hX : IsUnit ((designMatrix c pB)ᵀ * designMatrix c pB)) (γ α τ : ℝ) {ε : Ω → ι → ℝ}
    (hint : ∀ i, Integrable (fun ω => ε ω i) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∫ ω, contaminationEstimate c pB (designMatrix c pB *ᵥ ![γ, α, τ] + ε ω) ∂μ = α :=
  integral_olsEstimator_apply hX ![γ, α, τ] hint hmean 1

/-- **Null law of the contamination `t` statistic**: if there is no contamination (`α = 0`), so
that `BAF = γ + τ 1(g = AA) + ε` with i.i.d. `N(0, σ²)` errors (`σ > 0`), and the design has full
rank with more than three markers, then `contaminationTStatistic` has Student's `t` law with
`n - 3` degrees of freedom, whatever `γ` and `τ`. -/
theorem hasLaw_contaminationTStatistic {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (c : ι → Bool) (pB : ι → ℝ) (hX : IsUnit ((designMatrix c pB)ᵀ * designMatrix c pB))
    (hn : 3 < Fintype.card ι) (γ τ : ℝ) {ε : Ω → ι → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : ι => gaussianReal 0 1) μ) :
    HasLaw (fun ω => contaminationTStatistic c pB (designMatrix c pB *ᵥ ![γ, 0, τ] + ε ω))
      (studentTMeasure (Fintype.card ι - 3)) μ := by
  have key : ∀ y, coefficientTStatistic (designMatrix c pB) 1 0 y =
      coefficientTStatistic (designMatrix c pB) 1 ![γ, 0, τ] y := by
    intro y
    simp [coefficientTStatistic]
  have h := hasLaw_coefficientTStatistic hX (by simpa using hn) ![γ, 0, τ] hσ hε 1
  rw [Fintype.card_fin] at h
  simp only [contaminationTStatistic, key]
  exact h

/-- **Level of the one-sided contamination test**: under the null hypothesis `α = 0` of
`hasLaw_contaminationTStatistic`, the probability that the `t` statistic exceeds a threshold `t₀`
is the upper tail `P(T > t₀)` of Student's `t` law with `n - 3` degrees of freedom. -/
theorem measureReal_lt_contaminationTStatistic {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (c : ι → Bool) (pB : ι → ℝ) (hX : IsUnit ((designMatrix c pB)ᵀ * designMatrix c pB))
    (hn : 3 < Fintype.card ι) (γ τ : ℝ) {ε : Ω → ι → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : ι => gaussianReal 0 1) μ)
    (t₀ : ℝ) :
    μ.real {ω | t₀ < contaminationTStatistic c pB (designMatrix c pB *ᵥ ![γ, 0, τ] + ε ω)} =
      (studentTMeasure (Fintype.card ι - 3)).real (Set.Ioi t₀) :=
  (hasLaw_contaminationTStatistic c pB hX hn γ τ hσ hε).measureReal_eq (p := fun t => t₀ < t)
    measurableSet_Ioi

/-! ### The minor-allele covariate -/

/-- The label of an allele under an orientation of the labels: alleles are coded `true` for the
minor allele and `false` for the major one, and the orientation `θ` is `true` when the label `B`
sits on the minor allele. `toAB θ x` is `true` when the allele `x` carries the label `B`. The
definition only uses the coding: `true` is the minor allele when its frequency is at most `1/2`. -/
def toAB (θ x : Bool) : Bool := if θ then x else !x

/-- A genotype `g`, coded by minor (`true`) and major (`false`) alleles, in the array's `A`/`B`
labels under the orientation `θ` (`true`: `B` is the minor allele). -/
def toABGenotype (θ : Bool) (g : Bool × Bool) : Bool × Bool := (toAB θ g.1, toAB θ g.2)

/-- The minor-allele model of a marker, as a joint law of the orientation `θ` of the labels
(`true`: `B` is the minor allele), the target's genotype `g₁` and the contaminant's genotype `g₂`,
both coded by minor (`true`) and major (`false`) alleles. In a population with genotype law `G`,
whose allele coded `true` has frequency `gamete G true` (the minor allele frequency when it is at
most `1/2`):

* the label `B` sits on the minor allele with probability `1/2`, independently of the genotypes
  (exchangeable labels);
* the target's genotype follows the Hardy–Weinberg proportions `offspring G`;
* the contaminant's two alleles are drawn independently of the target's genotype from the
  population allele frequencies `gamete G` (`markerLaw`). -/
noncomputable def minorAlleleLaw (G : PMF (Bool × Bool)) :
    PMF (Bool × (Bool × Bool) × (Bool × Bool)) :=
  (PMF.uniformFintype Bool).bind fun θ => (markerLaw (offspring G) (gamete G)).map (Prod.mk θ)

private theorem minorAlleleLaw_apply (G : PMF (Bool × Bool))
    (x : Bool × (Bool × Bool) × (Bool × Bool)) :
    minorAlleleLaw G x = 2⁻¹ * markerLaw (offspring G) (gamete G) x.2 := by
  rw [minorAlleleLaw, bind_map_prodMk_apply]
  simp

/-- **Conditional mean of the modelled BAF at `AA` markers with the minor-allele covariate** (Jun
et al. 2012): if the label `B` sits on the minor allele with probability `1/2` independently of the
genotypes, the target's genotype follows Hardy–Weinberg proportions and the contaminant's two
alleles are drawn independently from the population allele frequencies (`minorAlleleLaw`), then at
a marker where the target's genotype `g`, in `A`/`B` labels, is `AA`

`E[BAF | g = AA] = α f (1 - f) / ((1 - f)² + f²)`

for the modelled BAF `baf`, where `f = gamete G true` is the minor allele frequency. The identity
holds for every `f ∈ [0, 1]`: `f ≤ 1/2`, which makes the allele coded `true` the minor one, is not
needed. -/
theorem integral_baf_cond_minorAllele (α : ℝ) (G : PMF (Bool × Bool)) :
    ∫ x, baf α (toABGenotype x.1 x.2.1) (toABGenotype x.1 x.2.2)
        ∂((minorAlleleLaw G).toMeasure[|{x | toABGenotype x.1 x.2.1 = (false, false)}]) =
      α * (gamete G true).toReal * (1 - (gamete G true).toReal) /
        ((1 - (gamete G true).toReal) ^ 2 + (gamete G true).toReal ^ 2) := by
  classical
  have h := freq_true_add_freq_false G
  set f := (gamete G true).toReal with hf
  have hq : (gamete G false).toReal = 1 - f := by linarith
  rw [integral_cond_toMeasure]
  simp only [toABGenotype, toAB, Prod.mk.injEq, Bool.ite_eq_false_distrib,
    Bool.not_eq_eq_eq_not, Bool.not_false, Set.mem_ofPred_eq, minorAlleleLaw_apply,
    markerLaw_apply, iidGenotype_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, baf_eq, countB, Nat.cast_add, Fintype.sum_prod_type, Fintype.univ_bool,
    Finset.sum_ite_irrel, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, ← hf, Bool.not_true, Bool.ite_false_right, Bool.decide_eq_true,
    Bool.and_true, Finset.sum_singleton, hq, Bool.ite_true_right, Bool.or_false,
    add_self_div_two, Finset.sum_const_zero, offspring_apply, ite_false_left, Bool.not_eq_true,
    and_true, Bool.false_eq_true, ite_false_right, and_self, Bool.eq_false_and_eq_true_self,
    ↓reduceIte, add_zero, Bool.eq_true_and_eq_false_self, zero_add, Bool.toNat_false,
    CharP.cast_eq_zero, mul_zero, Bool.toNat_true, Nat.cast_one, mul_one, one_div]
  have hpos : 0 < (1 - f) ^ 2 + f ^ 2 := by nlinarith [sq_nonneg (2 * f - 1)]
  rw [div_eq_div_iff ?_ hpos.ne']
  · ring
  · intro hD
    have : ((1 - f) ^ 2 + f ^ 2) / 2 = 0 := by linear_combination hD
    linarith

/-- The law of the target's genotype in the array's `A`/`B` labels, which is taken to be its
genotype call, given the orientation `θ` of the labels (`true`: `B` is the minor allele), when the
target's genotype, coded by minor and major alleles, follows the Hardy–Weinberg proportions
`offspring G`. -/
noncomputable def callLikelihood (G : PMF (Bool × Bool)) : Kernel Bool (Bool × Bool) :=
  Kernel.ofFunOfCountable fun θ => ((offspring G).map (toABGenotype θ)).toMeasure

instance (G : PMF (Bool × Bool)) : IsMarkovKernel (callLikelihood G) :=
  ⟨fun θ => by
    change IsProbabilityMeasure (((offspring G).map (toABGenotype θ)).toMeasure)
    infer_instance⟩

/-- **Probability that the target is `AA` when `B` is the minor allele**: if the target's
genotype follows the Hardy–Weinberg proportions `offspring G`, then its genotype `g` in `A`/`B`
labels satisfies `P(g = AA | B minor) = (1 - f)²`, the proportion of the major homozygote, where
`1 - f = gamete G false` is the major allele frequency (the frequency of the allele coded `false`
for every `G`). -/
theorem callLikelihood_true_homA (G : PMF (Bool × Bool)) :
    callLikelihood G true {(false, false)} = gamete G false ^ 2 := by
  change ((offspring G).map (toABGenotype true)).toMeasure {(false, false)} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.map_apply, tsum_fintype]
  simp [toABGenotype, toAB, offspring_apply, sq]

/-- **Probability that the target is `AA` when `A` is the minor allele**: if the target's
genotype follows the Hardy–Weinberg proportions `offspring G`, then its genotype `g` in `A`/`B`
labels satisfies `P(g = AA | A minor) = f²`, the proportion of the minor homozygote, where
`f = gamete G true` is the minor allele frequency (the frequency of the allele coded `true` for
every `G`). -/
theorem callLikelihood_false_homA (G : PMF (Bool × Bool)) :
    callLikelihood G false {(false, false)} = gamete G true ^ 2 := by
  change ((offspring G).map (toABGenotype false)).toMeasure {(false, false)} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.map_apply, tsum_fintype]
  simp [Fintype.sum_prod_type, toABGenotype, toAB, offspring_apply, sq]

/-- **Posterior probability that `B` is the minor allele when the target is `AA`** (Jun et al.
2012), by Bayes' rule: with the label `B` on the minor allele with prior probability `1/2` and the
target's genotype in Hardy–Weinberg proportions, the posterior probability, under Mathlib's
posterior kernel, that `B` is the minor allele given that the target's genotype `g`, in `A`/`B`
labels, is `AA` is `P(B minor | g = AA) = (1 - f)² / ((1 - f)² + f²)`, where `f = gamete G true`
is the minor allele frequency (the frequency of the allele coded `true` for every `G`). -/
theorem posterior_callLikelihood_homA (G : PMF (Bool × Bool)) :
    (((callLikelihood G)†(PMF.uniformFintype Bool).toMeasure) (false, false)).real {true} =
      (1 - (gamete G true).toReal) ^ 2 /
        ((1 - (gamete G true).toReal) ^ 2 + (gamete G true).toReal ^ 2) := by
  have hμ : ∀ θ, (PMF.uniformFintype Bool).toMeasure {θ} = 2⁻¹ := by
    intro θ
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp
  have hsum : gamete G false + gamete G true = 1 := by
    have := (gamete G).tsum_coe
    rwa [tsum_fintype, Fintype.sum_bool, add_comm] at this
  have hx : (callLikelihood G ∘ₘ (PMF.uniformFintype Bool).toMeasure) {(false, false)} ≠ 0 := by
    rw [comp_apply_singleton_eq_tsum, tsum_bool, hμ, hμ, callLikelihood_true_homA,
      callLikelihood_false_homA]
    intro h0
    simp only [add_eq_zero, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top, false_or,
      pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h0
    rw [h0.1, h0.2, zero_add] at hsum
    exact zero_ne_one hsum
  have hq : (gamete G false).toReal = 1 - (gamete G true).toReal := by
    linarith [freq_true_add_freq_false G]
  rw [Measure.real, posterior_eq_bayesPosterior _ _ hx, bayesPosterior_apply_singleton, tsum_bool,
    hμ, hμ, callLikelihood_true_homA, callLikelihood_false_homA, ← mul_add,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num), add_comm (gamete G true ^ 2),
    ENNReal.toReal_div, ENNReal.toReal_add (ENNReal.pow_ne_top (PMF.apply_ne_top _ _))
      (ENNReal.pow_ne_top (PMF.apply_ne_top _ _)), ENNReal.toReal_pow, ENNReal.toReal_pow, hq]

end Domains.Biology.StatisticalGenetics.BAFContamination
