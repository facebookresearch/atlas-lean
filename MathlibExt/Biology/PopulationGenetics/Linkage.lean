/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Linkage disequilibrium and Haldane's map function

Two biallelic loci with alleles `A`/`a` and `B`/`b`. A gamete is a pair `g : Bool × Bool`
(`true` = `A` at the first locus, `true` = `B` at the second), and `x : Bool × Bool → ℝ` are the
gamete frequencies `x_AB, x_Ab, x_aB, x_ab`. Under random mating with recombination fraction
`r`, a gamete transmitted by an individual is, with probability `1 - r`, a copy of one of the
two parental gametes, and with probability `r` a recombinant carrying the first-locus allele of
one parental gamete and the second-locus allele of the other; the parental gametes are drawn
independently from `x`. Hence `recombine r x g = (1 - r) x_g + r p_{g.1} q_{g.2}`, where `p`,
`q` are the allele frequencies at the two loci. The linkage disequilibrium is
`D = x_AB x_ab - x_Ab x_aB`.

Haldane's map function: with no crossover interference the number of crossovers in an interval
of map length `d` Morgans is Poisson with mean `d`, and the two ends recombine iff the number of
crossovers is odd, so `r = P(Poisson(d) is odd) = (1 - e^{-2d}) / 2`.

## Main results

* `recombine_eq_sub`: `x'_AB = x_AB - r D`, `x'_ab = x_ab - r D`, `x'_Ab = x_Ab + r D`,
  `x'_aB = x_aB + r D`.
* `alleleFreqFst_recombine`, `alleleFreqSnd_recombine`: allele frequencies are unchanged.
* `linkageDiseq_recombine`: `D' = (1 - r) D`; `linkageDiseq_iterate`: `D_t = (1 - r)^t D_0`;
  `tendsto_linkageDiseq_iterate`: `D_t → 0` for `0 < r ≤ 1`.
* `hasSum_poisson_odd`, `poissonMeasure_real_odd`: Haldane's map function
  `∑_{k odd} e^{-d} d^k / k! = (1 - e^{-2d}) / 2`.
* `haldane_lt_half`, `tendsto_haldane_atTop`, `haldane_neg_half_log`, `neg_half_log_haldane`:
  `r < 1/2`, `r → 1/2` as `d → ∞`, and the inverse map `d = -½ log(1 - 2r)`.

## References

* J. B. S. Haldane, *The combination of linkage values, and the calculation of distances
  between the loci of linked factors*, J. Genet. 8 (1919), 299–309.
-/

@[expose] public section

open Filter Real Topology ProbabilityTheory
open scoped NNReal Nat

namespace MathlibExt.Biology.PopulationGenetics.Linkage

/-! ### Two-locus random mating -/

private theorem sum_four (x : Bool × Bool → ℝ) :
    ∑ g, x g = x (true, true) + x (true, false) + x (false, true) + x (false, false) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The frequency `∑ b, x (a, b)` of allele `a` at the first locus. -/
def alleleFreqFst (x : Bool × Bool → ℝ) (a : Bool) : ℝ := ∑ b, x (a, b)

/-- The frequency `∑ a, x (a, b)` of allele `b` at the second locus. -/
def alleleFreqSnd (x : Bool × Bool → ℝ) (b : Bool) : ℝ := ∑ a, x (a, b)

/-- The linkage disequilibrium `D = x_AB x_ab - x_Ab x_aB`. -/
def linkageDiseq (x : Bool × Bool → ℝ) : ℝ :=
  x (true, true) * x (false, false) - x (true, false) * x (false, true)

/-- One generation of random mating with recombination fraction `r`:
`recombine r x g = (1 - r) x_g + r p_{g.1} q_{g.2}`. -/
def recombine (r : ℝ) (x : Bool × Bool → ℝ) (g : Bool × Bool) : ℝ :=
  (1 - r) * x g + r * (alleleFreqFst x g.1 * alleleFreqSnd x g.2)

/-- The classical form of the recursion: coupling gametes (`AB`, `ab`) lose `r D` and repulsion
gametes (`Ab`, `aB`) gain `r D`. This identity holds for every real `r`; the biological domain
is `0 ≤ r ≤ 1/2`. -/
theorem recombine_eq_sub {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (r : ℝ) (g : Bool × Bool) :
    recombine r x g = x g - (if g.1 = g.2 then 1 else -1) * r * linkageDiseq x := by
  rw [sum_four] at hx
  obtain ⟨a, b⟩ := g
  cases a <;> cases b <;>
    simp only [recombine, alleleFreqFst, alleleFreqSnd, linkageDiseq, Fintype.sum_bool] <;>
    norm_num <;> linear_combination r * x (_, _) * hx

/-- Recombination keeps gamete frequencies summing to `1`. -/
theorem sum_recombine {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (r : ℝ) :
    ∑ g, recombine r x g = 1 := by
  rw [sum_four] at hx
  simp only [sum_four, recombine, alleleFreqFst, alleleFreqSnd, Fintype.sum_bool]
  linear_combination (1 - r + r * (x (true, true) + x (true, false) + x (false, true) +
    x (false, false) + 1)) * hx

/-- Recombination keeps gamete frequencies nonnegative for `0 ≤ r ≤ 1`. -/
theorem recombine_nonneg {x : Bool × Bool → ℝ} (hx : ∀ g, 0 ≤ x g) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (g : Bool × Bool) : 0 ≤ recombine r x g :=
  add_nonneg (mul_nonneg (sub_nonneg.2 hr1) (hx g)) (mul_nonneg hr0 (mul_nonneg
    (Finset.sum_nonneg fun _ _ => hx _) (Finset.sum_nonneg fun _ _ => hx _)))

/-- Allele frequencies at the first locus are unchanged by random mating (for every real
`r`). -/
theorem alleleFreqFst_recombine {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (r : ℝ) (a : Bool) :
    alleleFreqFst (recombine r x) a = alleleFreqFst x a := by
  rw [sum_four] at hx
  cases a <;> simp only [recombine, alleleFreqFst, alleleFreqSnd, Fintype.sum_bool] <;>
    linear_combination r * (x (_, true) + x (_, false)) * hx

/-- Allele frequencies at the second locus are unchanged by random mating (for every real
`r`). -/
theorem alleleFreqSnd_recombine {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (r : ℝ) (b : Bool) :
    alleleFreqSnd (recombine r x) b = alleleFreqSnd x b := by
  rw [sum_four] at hx
  cases b <;> simp only [recombine, alleleFreqFst, alleleFreqSnd, Fintype.sum_bool] <;>
    linear_combination r * (x (true, _) + x (false, _)) * hx

/-- Linkage disequilibrium decays by the factor `1 - r` per generation: `D' = (1 - r) D`
(for every real `r`). -/
theorem linkageDiseq_recombine {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (r : ℝ) :
    linkageDiseq (recombine r x) = (1 - r) * linkageDiseq x := by
  have h := hx
  rw [sum_four] at h
  rw [linkageDiseq, recombine_eq_sub hx, recombine_eq_sub hx, recombine_eq_sub hx,
    recombine_eq_sub hx]
  norm_num
  unfold linkageDiseq
  linear_combination
    (-(r * (x (true, true) * x (false, false) - x (true, false) * x (false, true)))) * h

/-- After `t` generations, `D_t = (1 - r)^t D_0`. -/
theorem linkageDiseq_iterate {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (r : ℝ) (t : ℕ) :
    linkageDiseq ((recombine r)^[t] x) = (1 - r) ^ t * linkageDiseq x := by
  have hsum : ∀ n : ℕ, ∑ g, (recombine r)^[n] x g = 1 := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact sum_recombine ih r
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', linkageDiseq_recombine (hsum t), ih, pow_succ]
    ring

/-- Linkage disequilibrium tends to `0` whenever `0 < r ≤ 1`; this contains the biological
range `0 < r ≤ 1/2`. For `r = 0` (complete linkage) `D` is constant. -/
theorem tendsto_linkageDiseq_iterate {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    Tendsto (fun t : ℕ => linkageDiseq ((recombine r)^[t] x)) atTop (𝓝 0) := by
  simp only [linkageDiseq_iterate hx]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.2 hr1)
    (sub_lt_self 1 hr0)).mul_const (linkageDiseq x)

/-! ### Haldane's map function -/

/-- Haldane's map function `r(d) = (1 - e^{-2d}) / 2`: the recombination fraction between two
loci at map distance `d` Morgans when crossovers form a Poisson process (no interference). -/
noncomputable def haldane (d : ℝ) : ℝ := (1 - exp (-2 * d)) / 2

/-- The probability that a Poisson count of mean `d` is odd, as a series:
`∑_{k odd} e^{-d} d^k / k! = (1 - e^{-2d}) / 2` (Haldane 1919). The series identity holds for
every real `d`; it is a probability for `0 ≤ d`. -/
theorem hasSum_poisson_odd (d : ℝ) :
    HasSum (fun k : ℕ => if Odd k then exp (-d) * d ^ k / k ! else 0) (haldane d) := by
  have hpos : exp (-d) * exp d = 1 := by rw [← exp_add]; simp
  have hneg : exp (-d) * exp (-d) = exp (-2 * d) := by
    rw [← exp_add]
    congr 1
    ring
  have hsum : exp (-d) * sinh d = haldane d := by
    rw [sinh_eq, haldane, ← mul_div_assoc, mul_sub, hpos, hneg]
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro m n h
    dsimp only at h
    omega
  apply (hinj.hasSum_iff ?_).mp
  · simpa only [Function.comp_def, ite_eq_left (odd_two_mul_add_one _), mul_div_assoc,
      hsum]
      using (Real.hasSum_sinh d).mul_left (exp (-d))
  · intro k hk
    have hodd : ¬ Odd k := by
      simpa only [range_two_mul_add_one, Set.mem_ofPred_eq] using hk
    simp only [ite_eq_right hodd]

/-- Haldane's map function (Haldane 1919): if the number of crossovers in an interval of map
length `d` Morgans is Poisson with mean `d`, the probability of an odd number of crossovers,
i.e. of recombination between the ends of the interval, is `(1 - e^{-2d}) / 2`. -/
theorem poissonMeasure_real_odd (d : ℝ≥0) :
    (poissonMeasure d).real {k | Odd k} = haldane d := by
  have hsum := hasSum_poisson_odd (d : ℝ)
  have hnonneg : ∀ k : ℕ, 0 ≤ if Odd k then exp (-(d : ℝ)) * (d : ℝ) ^ k / k ! else 0 :=
    fun k => by split_ifs <;> positivity
  rw [MeasureTheory.measureReal_def, poissonMeasure,
    MeasureTheory.Measure.sum_apply _ MeasurableSet.of_discrete]
  have hterms :
      (∑' k : ℕ, (ENNReal.ofReal (exp (-(d : ℝ)) * (d : ℝ) ^ k / k !) •
        MeasureTheory.Measure.dirac k) {k | Odd k}) =
      ∑' k : ℕ, ENNReal.ofReal (if Odd k then exp (-(d : ℝ)) * (d : ℝ) ^ k / k ! else 0) := by
    apply tsum_congr
    intro k
    by_cases hk : Odd k <;>
      simp [MeasureTheory.Measure.smul_apply, Set.indicator, hk]
  rw [hterms, ← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.summable, hsum.tsum_eq,
    ENNReal.toReal_ofReal (hsum.nonneg hnonneg)]

/-- Haldane's map function is nonnegative at nonnegative distances. -/
theorem haldane_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ haldane d := by
  have : exp (-2 * d) ≤ 1 := exp_le_one_iff.2 (by linarith)
  unfold haldane
  linarith

/-- The recombination fraction is always below `1/2` (for every real `d`). -/
theorem haldane_lt_half (d : ℝ) : haldane d < 1 / 2 := by
  unfold haldane
  have h := exp_pos (-2 * d)
  linarith

/-- Loci far apart are unlinked in the limit: `r → 1/2` as `d → ∞`. -/
theorem tendsto_haldane_atTop : Tendsto haldane atTop (𝓝 (1 / 2)) := by
  have hlinear : Tendsto (fun d : ℝ => -2 * d) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num)
  have hexp := Real.tendsto_exp_atBot.comp hlinear
  change Tendsto (fun d : ℝ => (1 - exp (-2 * d)) / 2) atTop (𝓝 (1 / 2))
  simpa only [Function.comp_def, sub_zero] using (hexp.const_sub 1).div_const 2

/-- The inverse map function `d = -½ log(1 - 2r)` recovers the map distance. -/
theorem neg_half_log_haldane (d : ℝ) : -(1 / 2) * log (1 - 2 * haldane d) = d := by
  have : 1 - 2 * haldane d = exp (-2 * d) := by unfold haldane; ring
  rw [this, log_exp]
  ring

/-- Every `r < 1/2` is the recombination fraction at the distance `-½ log(1 - 2r)`. The
hypothesis keeps `log` on positive arguments: at `r = 1/2` the right side would use the junk
value `log 0 = 0`. The distance is nonnegative exactly when `0 ≤ r`. -/
theorem haldane_neg_half_log {r : ℝ} (hr : r < 1 / 2) :
    haldane (-(1 / 2) * log (1 - 2 * r)) = r := by
  have h : -2 * (-(1 / 2) * log (1 - 2 * r)) = log (1 - 2 * r) := by ring
  rw [haldane, h, exp_log (by linarith)]
  ring

end MathlibExt.Biology.PopulationGenetics.Linkage
