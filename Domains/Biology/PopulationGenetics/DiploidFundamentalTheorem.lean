/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Selection
public import Domains.Biology.StatisticalGenetics.FisherDecomposition

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Fisher's fundamental theorem with the additive genetic variance (diploid, one locus)

One autosomal locus with a finite set `ι` of alleles, random mating (Hardy–Weinberg proportions
at birth), viability selection with symmetric genotype fitnesses `w i j = w j i`, and Mendelian
transmission: one generation maps the allele frequencies `p` to `p' = diploidSelect p w`
(`Selection.lean`), with mean fitness `w̄ = diploidMeanFitness p w`.

The model's domain is `IsDiploidModel p w`: the allele frequencies lie in the probability
simplex (`0 ≤ p i`, `∑ i, p i = 1`), the genotype fitnesses are nonnegative and symmetric, and
the mean fitness is positive. The results about selection assume it. Off the simplex `p` is not an
allele-frequency distribution, and the quantity `addVar p w` called the additive genetic variance
below can be negative.

Reading the genotype fitnesses as genotypic values, `FisherDecomposition.lean` gives Fisher's
average effect (average excess) of allele `i` in fitness, `α i = avgEffect p w i`, the dominance
deviations `δ i j = domDev p w i j`, and the additive genetic variance in fitness
`V_A = addVar p w = 2 ∑ i, p i α i ^ 2`.

## Main results

* `IsDiploidModel`: the model domain above.
* `marginalFitness_eq_add_avgEffect`: the marginal fitness of allele `i` is `w̄ + α i`, an
  algebraic identity that holds for every real `p`.
* `diploidSelect_sub_eq`: `Δp_i = p_i α_i / w̄`.
* `two_mul_sum_avgEffect_mul_diploidSelect_sub`: **Fisher's fundamental theorem** in the exact
  partial-change form (Price 1972; Ewens 1989): the change in mean fitness attributable to the
  change of allele frequencies with the average effects held fixed,
  `2 ∑ i, α i Δp_i`, equals `V_A / w̄`.
* `diploidMeanFitness_diploidSelect_sub_eq`: the total discrete change is not `V_A / w̄` in
  general: `w̄(p') - w̄(p) = V_A / w̄ + (∑ i, ∑ j, p i p j α i α j δ i j) / w̄ ^ 2`.
* `diploidMeanFitness_diploidSelect_sub_of_domDev_eq_zero`: with no dominance deviations the
  total change equals `V_A / w̄`.

## References

* R. A. Fisher, *The Genetical Theory of Natural Selection*, Clarendon Press, Oxford, 1930.
* G. R. Price, *Fisher's 'fundamental theorem' made clear*, Ann. Hum. Genet. 36 (1972), 129–140.
* W. J. Ewens, *An interpretation and proof of the fundamental theorem of natural selection*,
  Theor. Popul. Biol. 36 (1989), 167–180.
* S. Lessard, *Fisher's fundamental theorem of natural selection revisited*, Theor. Popul. Biol.
  52 (1997), 119–136 (the discrete-generation partial change, pp. 120–121, and
  `w̄ Δp_i = p_i a_i`, eq. 12).
-/

@[expose] public section

open Finset
open MathlibExt.Biology.PopulationGenetics.Selection
open MathlibExt.Biology.StatisticalGenetics.FisherDecomposition

namespace Domains.Biology.PopulationGenetics.DiploidFundamentalTheorem

/-- **Domain of the diploid viability-selection model.** The allele frequencies `p` lie in the
probability simplex, the genotype fitnesses `w` are nonnegative and symmetric, and the mean
fitness is positive. -/
structure IsDiploidModel {ι : Type*} [Fintype ι] (p : ι → ℝ) (w : ι → ι → ℝ) : Prop where
  /-- Every allele frequency is nonnegative. -/
  freq_nonneg : ∀ i, 0 ≤ p i
  /-- The allele frequencies sum to `1`. -/
  sum_freq : ∑ i, p i = 1
  /-- Every genotype fitness is nonnegative. -/
  fitness_nonneg : ∀ i j, 0 ≤ w i j
  /-- The fitness of a genotype does not depend on the order of its two genes. -/
  fitness_symm : ∀ i j, w i j = w j i
  /-- The mean fitness is positive. -/
  meanFitness_pos : 0 < diploidMeanFitness p w

/-- **Mean genotypic value in fitness.** The mean genotypic value of `FisherDecomposition`,
applied to genotype fitnesses, is the diploid mean fitness of `Selection`. -/
theorem meanValue_eq_diploidMeanFitness {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (w : ι → ι → ℝ) : meanValue p w = diploidMeanFitness p w := by
  rfl

/-- **Marginal fitness as mean fitness plus average effect.** For symmetric genotype fitnesses,
the marginal fitness of allele `i` is the mean fitness plus the average effect (average excess)
of `i` in fitness: `m_i = w̄ + α_i`. This is an algebraic identity of the definitions; it holds
for every real `p`, in the model domain or not. -/
theorem marginalFitness_eq_add_avgEffect {ι : Type*} [Fintype ι] {p : ι → ℝ}
    {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i) (i : ι) :
    marginalFitness p w i = diploidMeanFitness p w + avgEffect p w i := by
  rw [marginalFitness_of_symm hw, avgEffect, meanValue_eq_diploidMeanFitness]
  simp only [mul_comm]
  ring

/-- **Allele-frequency change under diploid selection.** In the model domain, one generation of
diploid viability selection changes the frequency of allele `i` by `Δp_i = p_i α_i / w̄`. -/
theorem diploidSelect_sub_eq {ι : Type*} [Fintype ι] {p : ι → ℝ} {w : ι → ι → ℝ}
    (hm : IsDiploidModel p w) (i : ι) :
    diploidSelect p w i - p i = p i * avgEffect p w i / diploidMeanFitness p w := by
  have hW := hm.meanFitness_pos.ne'
  rw [diploidSelect, marginalFitness_eq_add_avgEffect hm.fitness_symm]
  field_simp [hW]
  ring

/-- **Fisher's fundamental theorem with the additive genetic variance.** Fisher's fundamental
theorem of natural selection (Fisher 1930), in the exact partial-change form of Price (1972) and
Ewens (1989): in the model domain, the change in mean fitness due to natural selection,
`2 ∑ i, α_i Δp_i` (the allele-frequency change weighted by the average effects in fitness, which
are held fixed), equals the additive genetic variance in fitness divided by the mean fitness,
`V_A / w̄`. -/
theorem two_mul_sum_avgEffect_mul_diploidSelect_sub {ι : Type*} [Fintype ι] {p : ι → ℝ}
    {w : ι → ι → ℝ} (hm : IsDiploidModel p w) :
    2 * ∑ i, avgEffect p w i * (diploidSelect p w i - p i) =
      addVar p w / diploidMeanFitness p w := by
  simp_rw [diploidSelect_sub_eq hm]
  unfold addVar
  rw [mul_div_assoc, sum_div]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

private theorem meanFitness_decomposition {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (w : ι → ι → ℝ) (hq : ∑ i, q i = 1) :
    diploidMeanFitness q w = diploidMeanFitness p w +
      2 * ∑ i, q i * avgEffect p w i + ∑ i, ∑ j, q i * q j * domDev p w i j := by
  calc
    diploidMeanFitness q w = ∑ i, ∑ j,
        ((q i * diploidMeanFitness p w) * q j + (q i * avgEffect p w i) * q j +
          q i * (q j * avgEffect p w j) + q i * q j * domDev p w i j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [genotypicValue_eq p w i j, meanValue_eq_diploidMeanFitness]
      ring
    _ = diploidMeanFitness p w + 2 * ∑ i, q i * avgEffect p w i +
        ∑ i, ∑ j, q i * q j * domDev p w i j := by
      simp only [sum_add_distrib, ← sum_mul_sum, ← sum_mul, hq, one_mul, mul_one]
      ring

private theorem selected_domDev_eq {ι : Type*} [Fintype ι] {p : ι → ℝ}
    {w : ι → ι → ℝ} (hm : IsDiploidModel p w) :
    (∑ i, ∑ j, diploidSelect p w i * diploidSelect p w j * domDev p w i j) =
      (∑ i, ∑ j, p i * p j * avgEffect p w i * avgEffect p w j * domDev p w i j) /
        diploidMeanFitness p w ^ 2 := by
  let d : ι → ℝ := fun i => p i * avgEffect p w i / diploidMeanFitness p w
  have hq (i : ι) : diploidSelect p w i = p i + d i := by
    have h := diploidSelect_sub_eq hm i
    dsimp [d]
    exact ((sub_eq_iff_eq_add).mp h).trans (add_comm _ _)
  have hr (a : ι → ℝ) : (∑ i, ∑ j, a i * (p j * domDev p w i j)) = 0 := by
    simp only [← mul_sum, sum_mul_domDev_right hm.sum_freq w, mul_zero, sum_const_zero]
  have hl : (∑ i, ∑ j, (p i * domDev p w i j) * d j) = 0 := by
    rw [sum_comm]
    simp only [← sum_mul, sum_mul_domDev_left hm.sum_freq hm.fitness_symm, zero_mul,
      sum_const_zero]
  calc
    (∑ i, ∑ j, diploidSelect p w i * diploidSelect p w j * domDev p w i j) =
        ∑ i, ∑ j, (p i * (p j * domDev p w i j) + d i * (p j * domDev p w i j) +
          (p i * domDev p w i j) * d j + d i * d j * domDev p w i j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [hq i, hq j]
      ring
    _ = ∑ i, ∑ j, d i * d j * domDev p w i j := by
      simp only [sum_add_distrib]
      rw [hr p, hr d, hl]
      ring
    _ = (∑ i, ∑ j,
        p i * p j * avgEffect p w i * avgEffect p w j * domDev p w i j) /
          diploidMeanFitness p w ^ 2 := by
      simp only [sum_div]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      dsimp [d]
      ring

/-- **Total change in mean fitness under diploid selection.** In the model domain, the total
change in mean fitness over one generation is the additive term `V_A / w̄` plus a dominance term:
`w̄(p') - w̄(p) = V_A / w̄ + (∑ i, ∑ j, p_i p_j α_i α_j δ_ij) / w̄ ^ 2`. In general the total
discrete change is therefore not `V_A / w̄`. -/
theorem diploidMeanFitness_diploidSelect_sub_eq {ι : Type*} [Fintype ι] {p : ι → ℝ}
    {w : ι → ι → ℝ} (hm : IsDiploidModel p w) :
    diploidMeanFitness (diploidSelect p w) w - diploidMeanFitness p w =
      addVar p w / diploidMeanFitness p w +
        (∑ i, ∑ j, p i * p j * avgEffect p w i * avgEffect p w j * domDev p w i j) /
          diploidMeanFitness p w ^ 2 := by
  have hα : (∑ i, avgEffect p w i * (diploidSelect p w i - p i)) =
      ∑ i, diploidSelect p w i * avgEffect p w i := by
    have hzero : (∑ i, avgEffect p w i * p i) = 0 := by
      simpa only [mul_comm] using sum_mul_avgEffect hm.sum_freq w
    simp only [mul_sub, sum_sub_distrib, hzero, sub_zero]
    simp only [mul_comm]
  have hpartial := two_mul_sum_avgEffect_mul_diploidSelect_sub hm
  rw [hα] at hpartial
  rw [meanFitness_decomposition p (diploidSelect p w) w
      (sum_diploidSelect hm.meanFitness_pos.ne'),
    selected_domDev_eq hm, hpartial]
  ring

/-- **Total change in mean fitness without dominance.** In the model domain with no dominance
deviations in fitness (fitnesses additive over the two genes), the total change in mean fitness
over one generation equals `V_A / w̄`. -/
theorem diploidMeanFitness_diploidSelect_sub_of_domDev_eq_zero {ι : Type*} [Fintype ι]
    {p : ι → ℝ} {w : ι → ι → ℝ} (hm : IsDiploidModel p w)
    (hδ : ∀ i j, domDev p w i j = 0) :
    diploidMeanFitness (diploidSelect p w) w - diploidMeanFitness p w =
      addVar p w / diploidMeanFitness p w := by
  rw [diploidMeanFitness_diploidSelect_sub_eq hm]
  simp only [hδ, mul_zero, sum_const_zero, zero_div, add_zero]

end Domains.Biology.PopulationGenetics.DiploidFundamentalTheorem
