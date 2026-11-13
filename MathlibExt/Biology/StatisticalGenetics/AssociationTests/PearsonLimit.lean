/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GoodnessOfFit.Pearson
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.StrongLaw

/-!
# Pearson's Hardy–Weinberg test with estimated allele frequency is asymptotically `χ²₁`

## Setup

A biallelic locus has alleles `A` and `a`. An individual's genotype class is the number
`i ∈ Fin 3 = {0, 1, 2}` of copies of `A` it carries (`aa`, `Aa`, `AA`). A sample of `N`
individuals gives genotype counts `n = (n₀, n₁, n₂)`, here `ProbabilityTheory.cellCount`.

**Hardy–Weinberg proportions** at allele frequency `p` (of `A`), with `q = 1 - p`, are the genotype
probabilities `hweProb p = (q², 2pq, p²)`. The test of the composite null "the genotype
probabilities are `hweProb p` for some `p`" estimates `p` by the sample allele frequency
`p̂ = (n₁ + 2 n₂) / (2 N)` (`alleleFreqHat`; the maximum-likelihood estimate under the null) and
refers Pearson's statistic `X² = ∑ᵢ (nᵢ - N hweProb p̂ i)² / (N hweProb p̂ i)` (`hweStat`, the
canonical `ProbabilityTheory.pearsonStatistic` evaluated at the fitted probabilities) to `χ²₁`.
The `3` cells have `2` free probabilities; fitting one parameter leaves `2 - 1 = 1` degree of
freedom.

## Main results

* `hweStat_eq_mul_inbreedingHat_sq`: the exact finite identity `X² = N F̂²`, where
  `F̂ = (4 n₀ n₂ - n₁²) / ((2 n₀ + n₁)(n₁ + 2 n₂))` (`inbreedingHat`) is the estimated inbreeding
  coefficient `1 - H_obs / H_exp`. It holds for all nonnegative counts summing to `N`, including
  the monomorphic tables where both sides are `0`; `inbreedingHat_eq_one_sub` identifies `F̂` with
  `1 - H_obs / H_exp` for polymorphic tables.
* `tendstoInDistribution_hweStat`: **Pearson's `X² → χ²₁` limit theorem for Hardy–Weinberg
  equilibrium with estimated allele frequency.** For i.i.d. genotypes in Hardy–Weinberg
  proportions with `0 < p < 1`, the fitted statistic converges in distribution to `χ²₁`.
* `tendstoInDistribution_pearsonStatistic_hweProb`: the contrast with `p` *known*: the simple-null
  statistic `∑ᵢ (nᵢ - N hweProb p i)² / (N hweProb p i)` converges to `χ²₂` (a specialization of
  the canonical `ProbabilityTheory.tendstoInDistribution_pearsonStatistic`). Estimating `p` costs
  exactly one degree of freedom.
* `hweStat_ae_eq_zero_of_monomorphic`, `not_tendstoInDistribution_hweStat_of_monomorphic`: at the
  boundary `p = 0` or `p = 1` the statistic is almost surely `0` for every `N`, so it has no
  `χ²₁` limit; the hypothesis `0 < p < 1` cannot be dropped.

## Method

With `Xₘ = 1{gₘ = 2}`, `Yₘ = gₘ / 2` (so `p̂ = Ȳ`), the estimated disequilibrium is
`D̂ = X̄ - Ȳ² = (4 n₀ n₂ - n₁²) / (4 N²)` and `F̂ = D̂ / (p̂ q̂)`. Under Hardy–Weinberg proportions
`E X = p²`, `E Y = p`, and the exact decomposition
`D̂ = W̄ - (Ȳ - p)²`, `Wₘ = Xₘ - 2p Yₘ + p²`, holds. The summand `W` is centered with variance
`p² q²`, so `√N W̄ / (p q) → N(0, 1)` by the central limit theorem, while
`√N (Ȳ - p)² = [√N (Ȳ - p)] (Ȳ - p) → 0` in probability (CLT for `Y` times the strong law).
The strong law also gives `p̂ q̂ → p q`. Slutsky's theorem yields `√N F̂ → N(0, 1)`, and
`X² = (√N F̂)²` converges to the square of a standard normal, i.e. to `χ²₁`
(`gaussianReal_map_sq`).

This direct route uses the exact identity `X² = N F̂²` rather than the general fitted-parameter
theorem `ProbabilityTheory.tendstoInDistribution_pearsonStatistic_fitted`: that theorem needs a
model `θ ↦ pθ θ` that is nonnegative for *every* `θ`, which the Hardy–Weinberg parametrization
`(q², 2pq, p²)` on all of `ℝ` is not (its docstring flags this exact case), plus the
efficient-estimator projection identity for `p̂`. Clamping the parameter to `[0, 1]`, as that
docstring suggests, would satisfy the nonnegativity hypothesis (the clamp is the identity near
`p ∈ (0, 1)`), but the derivative, the weighted Jacobian, and the projection identity would still
have to be built in `EuclideanSpace ℝ (Fin 3)`; that route was rejected as longer than the direct
proof, which also yields the exact identity `X² = N F̂²`.

## Boundary cases and scope

* `0 < p < 1` is needed: at `p ∈ {0, 1}` the locus is monomorphic and `X² = 0` almost surely
  (`not_tendstoInDistribution_hweStat_of_monomorphic`).
* The sample-size index `N` grows with `p` fixed; sparse-cell (rare-allele, `N p²` bounded)
  asymptotics, where the exact test is preferred, are not covered.
* Only the null limit is proved; the law of `X²` under alternatives (`F ≠ 0`) is not treated.
* The finite-sample discrepancy between `X²` and the exact (Levene–Haldane) test is the subject of
  a separate development and is not used here.

## Source receipt

Pearson's statistic is `ProbabilityTheory.pearsonStatistic` and the cell counts are
`ProbabilityTheory.cellCount` from `MathlibExt.Probability.Statistics.GoodnessOfFit.Pearson`,
reused unchanged. The degrees-of-freedom rule for estimated parameters is Fisher (1924); the
identity `X² = N F̂²` for the biallelic Hardy–Weinberg test and its `χ²₁` reference law are
standard (Weir 1996, Chapter 3; Emigh 1980). The CLT is Mathlib's
`tendstoInDistribution_inv_sqrt_mul_sum` / `tendstoInDistribution_inv_sqrt_mul_sum_sub`, the strong
law `strong_law_ae_real`, and Slutsky's theorem is from
`MathlibExt.Probability.Statistics.Slutsky`.

## References

* K. Pearson, *On the criterion that a given system of deviations …*, Philos. Mag. (5) 50 (1900),
  157–175.
* R. A. Fisher, *The conditions under which χ² measures the discrepancy between observation and
  hypothesis*, J. Roy. Statist. Soc. 87 (1924), 442–450.
* T. H. Emigh, *A comparison of tests for Hardy–Weinberg equilibrium*, Biometrics 36 (1980),
  627–642.
* B. S. Weir, *Genetic Data Analysis II*, Sinauer (1996), Chapter 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace MathlibExt.Biology.StatisticalGenetics.PearsonLimit

/-! ### Hardy–Weinberg proportions and the fitted statistic -/

/-- **Hardy–Weinberg genotype proportions** at allele frequency `p`: the probabilities
`((1 - p)², 2 p (1 - p), p²)` of carrying `0, 1, 2` copies of the counted allele. -/
def hweProb (p : ℝ) : Fin 3 → ℝ := ![(1 - p) ^ 2, 2 * p * (1 - p), p ^ 2]

/-- The **sample allele frequency** `p̂ = (n₁ + 2 n₂) / (2 (n₀ + n₁ + n₂))` of the counted allele
from genotype counts `n` (`0` when there are no individuals). -/
noncomputable def alleleFreqHat (n : Fin 3 → ℝ) : ℝ := (n 1 + 2 * n 2) / (2 * ∑ i, n i)

/-- **Pearson's Hardy–Weinberg statistic with estimated allele frequency**: Pearson's statistic of
the genotype counts `n` of `N` individuals against the Hardy–Weinberg proportions at the sample
allele frequency, `∑ᵢ (nᵢ - N hweProb p̂ i)² / (N hweProb p̂ i)`. -/
noncomputable def hweStat (N : ℕ) (n : Fin 3 → ℝ) : ℝ :=
  pearsonStatistic N (hweProb (alleleFreqHat n)) n

/-- The **estimated inbreeding coefficient**
`F̂ = (4 n₀ n₂ - n₁²) / ((2 n₀ + n₁)(n₁ + 2 n₂))`. For a polymorphic table it equals
`1 - H_obs / H_exp`, observed over Hardy–Weinberg-expected heterozygosity at `p̂`
(`inbreedingHat_eq_one_sub`); it is `0` for a monomorphic table, by `x / 0 = 0`. -/
noncomputable def inbreedingHat (n : Fin 3 → ℝ) : ℝ :=
  (4 * n 0 * n 2 - n 1 ^ 2) / ((2 * n 0 + n 1) * (n 1 + 2 * n 2))

@[simp] theorem hweProb_zero (p : ℝ) : hweProb p 0 = (1 - p) ^ 2 := rfl
@[simp] theorem hweProb_one (p : ℝ) : hweProb p 1 = 2 * p * (1 - p) := rfl
@[simp] theorem hweProb_two (p : ℝ) : hweProb p 2 = p ^ 2 := rfl

/-- Hardy–Weinberg proportions sum to `1`. -/
theorem sum_hweProb (p : ℝ) : ∑ i, hweProb p i = 1 := by
  simp only [Fin.sum_univ_three, hweProb_zero, hweProb_one, hweProb_two]
  ring

/-- For `0 < p < 1` every genotype class has positive Hardy–Weinberg probability. -/
theorem hweProb_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin 3) : 0 < hweProb p i := by
  have hq : 0 < 1 - p := by linarith
  fin_cases i
  · change 0 < (1 - p) ^ 2
    positivity
  · change 0 < 2 * p * (1 - p)
    positivity
  · change 0 < p ^ 2
    positivity

/-- For a polymorphic table (both alleles observed), the estimated inbreeding coefficient is
`1 - H_obs / H_exp` with observed heterozygosity `H_obs = n₁ / ∑ n` and Hardy–Weinberg-expected
heterozygosity `H_exp = 2 p̂ (1 - p̂)`. -/
theorem inbreedingHat_eq_one_sub {n : Fin 3 → ℝ} (h0 : 2 * n 0 + n 1 ≠ 0)
    (h2 : n 1 + 2 * n 2 ≠ 0) (hN : ∑ i, n i ≠ 0) :
    inbreedingHat n = 1 - (n 1 / ∑ i, n i) / (2 * alleleFreqHat n * (1 - alleleFreqHat n)) := by
  rw [Fin.sum_univ_three] at hN
  simp only [inbreedingHat, alleleFreqHat, Fin.sum_univ_three]
  generalize n 0 = a at *
  generalize n 1 = b at *
  generalize n 2 = c at *
  have hx : 2 * ((b + 2 * c) / (2 * (a + b + c))) * (1 - (b + 2 * c) / (2 * (a + b + c))) =
      (2 * a + b) * (b + 2 * c) / (2 * (a + b + c) ^ 2) := by
    field_simp; ring
  rw [hx]
  have hD : (2 * a + b) * (b + 2 * c) ≠ 0 := mul_ne_zero h0 h2
  generalize hDdef : (2 * a + b) * (b + 2 * c) = D at *
  field_simp
  rw [← hDdef]
  ring

/-- **The fitted Hardy–Weinberg statistic is `N F̂²`.** For nonnegative genotype counts `n` of `N`
individuals, Pearson's statistic against Hardy–Weinberg proportions at the sample allele frequency
equals `N` times the squared estimated inbreeding coefficient. Monomorphic tables (all
individuals of class `0`, or all of class `2`) and the empty table give `0` on both sides. -/
theorem hweStat_eq_mul_inbreedingHat_sq {N : ℕ} {n : Fin 3 → ℝ} (hn : ∀ i, 0 ≤ n i)
    (hN : ∑ i, n i = N) : hweStat N n = N * inbreedingHat n ^ 2 := by
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  rw [Fin.sum_univ_three] at hN
  simp only [hweStat, inbreedingHat, alleleFreqHat, pearsonStatistic, Fin.sum_univ_three,
    hweProb_zero, hweProb_one, hweProb_two, ← hN]
  generalize n 0 = a at *
  generalize n 1 = b at *
  generalize n 2 = c at *
  rcases eq_or_lt_of_le (add_nonneg (mul_nonneg zero_le_two h0) h1 : 0 ≤ 2 * a + b) with hA | hA
  · -- no `0`-alleles carried in classes `0, 1`: `a = b = 0`
    have ha : a = 0 := by linarith
    have hb : b = 0 := by linarith
    subst ha hb
    rcases eq_or_lt_of_le h2 with hc | hc
    · subst hc; simp
    · have : (0 + 2 * c) / (2 * (0 + 0 + c)) = 1 := by field_simp; ring
      rw [this]
      simp
  rcases eq_or_lt_of_le (add_nonneg h1 (mul_nonneg zero_le_two h2) : 0 ≤ b + 2 * c) with hB | hB
  · have hb : b = 0 := by linarith
    have hc : c = 0 := by linarith
    subst hb hc
    have : (0 + 2 * 0) / (2 * (a + 0 + 0)) = (0 : ℝ) := by simp
    rw [this]
    simp
  have hT : 0 < a + b + c := by linarith
  have e0 : (a + b + c) * (1 - (b + 2 * c) / (2 * (a + b + c))) ^ 2 =
      (2 * a + b) ^ 2 / (4 * (a + b + c)) := by
    field_simp; ring
  have e1 : (a + b + c) * (2 * ((b + 2 * c) / (2 * (a + b + c))) *
      (1 - (b + 2 * c) / (2 * (a + b + c)))) = (2 * a + b) * (b + 2 * c) / (2 * (a + b + c)) := by
    field_simp; ring
  have e2 : (a + b + c) * ((b + 2 * c) / (2 * (a + b + c))) ^ 2 =
      (b + 2 * c) ^ 2 / (4 * (a + b + c)) := by
    field_simp; ring
  rw [e0, e1, e2]
  have f0 : a - (2 * a + b) ^ 2 / (4 * (a + b + c)) = (4 * a * c - b ^ 2) / (4 * (a + b + c)) := by
    field_simp; ring
  have f1 : b - (2 * a + b) * (b + 2 * c) / (2 * (a + b + c)) =
      -(4 * a * c - b ^ 2) / (2 * (a + b + c)) := by
    field_simp; ring
  have f2 : c - (b + 2 * c) ^ 2 / (4 * (a + b + c)) = (4 * a * c - b ^ 2) / (4 * (a + b + c)) := by
    field_simp; ring
  have fT : a + b + c = ((2 * a + b) + (b + 2 * c)) / 2 := by ring
  rw [f0, f1, f2, fT]
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hAB : (2 * a + b) + (b + 2 * c) ≠ 0 := by linarith
  generalize 4 * a * c - b ^ 2 = K
  generalize 2 * a + b = A at *
  generalize b + 2 * c = B at *
  field_simp
  ring

/-! ### Per-individual summaries and the pathwise decomposition -/

/-- The allele fraction `i / 2` of genotype class `i`; its sample mean is `p̂`. -/
private noncomputable def yv : Fin 3 → ℝ := ![0, 1 / 2, 1]

/-- The centered disequilibrium summand `1{i = 2} - 2 p (i / 2) + p²`. -/
private def wv (p : ℝ) : Fin 3 → ℝ := ![p ^ 2, -(p * (1 - p)), (1 - p) ^ 2]

section Pathwise

variable {Ω : Type*} (X : ℕ → Ω → Fin 3) (N : ℕ) (ω : Ω)

private theorem sum_comp_eq_sum_cellCount (f : Fin 3 → ℝ) :
    ∑ m ∈ range N, f (X m ω) = ∑ i, f i * cellCount X N ω i := by
  simp only [cellCount, mul_sum, mul_ite, mul_one, mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_ite_eq]
  simp

private theorem cellCount_nonneg (i : Fin 3) : 0 ≤ cellCount X N ω i :=
  sum_nonneg fun _ _ => by split_ifs <;> norm_num

private theorem sum_cellCount : ∑ i, cellCount X N ω i = N := by
  simpa using (sum_comp_eq_sum_cellCount X N ω fun _ => 1).symm

/-- The sample mean of the allele fractions, `p̂`. -/
private noncomputable def meanY : ℝ := (∑ m ∈ range N, yv (X m ω)) / N

/-- The standardized disequilibrium sum `N^{-1/2} ∑ Wₘ / (p q)`. -/
private noncomputable def stdStat (p : ℝ) : ℝ :=
  (√N)⁻¹ * ∑ m ∈ range N, wv p (X m ω) / (p * (1 - p))

/-- The scaled centered allele-fraction sum `N^{-1/2} (∑ Yₘ - N p)`. -/
private noncomputable def cltY (p : ℝ) : ℝ := (√N)⁻¹ * (∑ m ∈ range N, yv (X m ω) - N * p)

/-- `√N F̂ · (p̂ q̂) / (p q)`: the standardized sum minus the quadratic correction. -/
private noncomputable def tStat (p : ℝ) : ℝ :=
  stdStat X N ω p + cltY X N ω p * ((p - meanY X N ω) / (p * (1 - p)))

/-- `(p̂ q̂)² / (p q)²`. -/
private noncomputable def vStat (p : ℝ) : ℝ :=
  (meanY X N ω * (1 - meanY X N ω)) ^ 2 / (p * (1 - p)) ^ 2

/-- The exact pathwise decomposition `X² = tStat² / vStat`, for every sample size. -/
private theorem hweStat_cellCount_eq {p : ℝ} (hp0 : p ≠ 0) (hp1 : 1 - p ≠ 0) :
    hweStat N (cellCount X N ω) = tStat X N ω p ^ 2 / vStat X N ω p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hweStat, pearsonStatistic, tStat, stdStat, cltY]
  rw [hweStat_eq_mul_inbreedingHat_sq (cellCount_nonneg X N ω) (sum_cellCount X N ω)]
  have hsum := sum_cellCount X N ω
  simp only [tStat, stdStat, cltY, vStat, meanY, ← sum_div]
  rw [sum_comp_eq_sum_cellCount X N ω (wv p), sum_comp_eq_sum_cellCount X N ω yv]
  simp only [Fin.sum_univ_three, wv, yv, inbreedingHat, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hsum ⊢
  rw [← hsum]
  have h0 := cellCount_nonneg X N ω 0
  have h1 := cellCount_nonneg X N ω 1
  have h2 := cellCount_nonneg X N ω 2
  generalize cellCount X N ω 0 = a at *
  generalize cellCount X N ω 1 = b at *
  generalize cellCount X N ω 2 = c at *
  have hT : 0 < a + b + c := by rw [hsum]; exact_mod_cast hN
  have hT' := hT.ne'
  have hss : √(a + b + c) ^ 2 = a + b + c := Real.sq_sqrt hT.le
  have hs : √(a + b + c) ≠ 0 := (Real.sqrt_pos.2 hT).ne'
  generalize √(a + b + c) = s at *
  have ht : s⁻¹ * ((p ^ 2 * a + -(p * (1 - p)) * b + (1 - p) ^ 2 * c) / (p * (1 - p))) +
      s⁻¹ * (0 * a + 1 / 2 * b + 1 * c - (a + b + c) * p) *
        ((p - (0 * a + 1 / 2 * b + 1 * c) / (a + b + c)) / (p * (1 - p))) =
      (4 * a * c - b ^ 2) / (4 * (a + b + c) * s * (p * (1 - p))) := by
    field_simp
    ring
  have hv : (0 * a + 1 / 2 * b + 1 * c) / (a + b + c) *
      (1 - (0 * a + 1 / 2 * b + 1 * c) / (a + b + c)) =
      (2 * a + b) * (b + 2 * c) / (4 * (a + b + c) ^ 2) := by
    field_simp
    ring
  rw [ht, hv]
  by_cases hAB : (2 * a + b) * (b + 2 * c) = 0
  · simp [hAB]
  rw [← hss]
  generalize 4 * a * c - b ^ 2 = K
  generalize (2 * a + b) * (b + 2 * c) = A at *
  field_simp

end Pathwise

/-! ### The asymptotic test -/

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → Fin 3} {p : ℝ}

/-- **Pearson's `X² → χ²₁` limit theorem for Hardy–Weinberg equilibrium with estimated allele
frequency.** Let the genotypes `X 0, X 1, …` (number of copies of the counted allele) be i.i.d. in
Hardy–Weinberg proportions `P(X 0 = i) = hweProb p i` at a polymorphic allele frequency
`0 < p < 1`. Then Pearson's statistic of the genotype counts of the first `N` individuals against
the Hardy–Weinberg proportions at the sample allele frequency `p̂`,
`hweStat N (cellCount X N) = ∑ᵢ (nᵢ - N hweProb p̂ i)² / (N hweProb p̂ i)`, converges in
distribution to `χ²₁` as `N → ∞`.

The proof writes `hweStat = N F̂²` (`hweStat_eq_mul_inbreedingHat_sq`), linearizes `√N F̂` around
the centered summand `1{X = 2} - p X + p²` (variance `p² (1 - p)²`), and applies the central limit
theorem, the strong law, and Slutsky's theorem. -/
theorem tendstoInDistribution_hweStat (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = hweProb p i)
    (hp0 : 0 < p) (hp1 : p < 1) (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution (fun N ω => hweStat N (cellCount X N ω)) atTop Z (fun _ => P) P' := by
  have hq : 0 < 1 - p := by linarith
  have hr : 0 < p * (1 - p) := mul_pos hp0 hq
  have hXm : ∀ m, AEMeasurable (X m) P := fun m => (hident m).aemeasurable_fst
  have hE := integral_comp_eq_sum_of_measureReal_preimage (hXm 0) hX0
  have hind : ∀ g : Fin 3 → ℝ, iIndepFun (fun m ω => g (X m ω)) P := fun g =>
    hindep.comp (fun _ => g) fun _ => Measurable.of_discrete
  have hid : ∀ g : Fin 3 → ℝ, ∀ m, IdentDistrib (fun ω => g (X m ω)) (fun ω => g (X 0 ω)) P P :=
    fun g m => (hident m).comp Measurable.of_discrete
  have hsum_meas : ∀ g : Fin 3 → ℝ, ∀ N, AEMeasurable (fun ω => ∑ m ∈ range N, g (X m ω)) P :=
    fun g N => Finset.aemeasurable_fun_sum _ fun m _ => Measurable.of_discrete.comp_aemeasurable
      (hXm m)
  -- Step 1: the standardized disequilibrium sum is asymptotically `N(0, 1)`.
  have h1 : TendstoInDistribution (fun N ω => stdStat X N ω p) atTop id (fun _ => P)
      (gaussianReal 0 1) := by
    refine tendstoInDistribution_inv_sqrt_mul_sum (X := fun m ω => wv p (X m ω) / (p * (1 - p)))
      HasLaw.id ?_ ?_ (hind fun i => wv p i / (p * (1 - p)))
      (hid fun i => wv p i / (p * (1 - p)))
    · rw [hE fun i => wv p i / (p * (1 - p))]
      simp only [Fin.sum_univ_three, hweProb_zero, hweProb_one, hweProb_two, wv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      field_simp
      ring
    · change ∫ ω, (wv p (X 0 ω) / (p * (1 - p))) ^ 2 ∂P = 1
      rw [hE fun i => (wv p i / (p * (1 - p))) ^ 2]
      simp only [Fin.sum_univ_three, hweProb_zero, hweProb_one, hweProb_two, wv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      have : p * (1 - p) ≠ 0 := hr.ne'
      field_simp
      ring
  -- Step 2: the quadratic correction `√N (p̂ - p)²` tends to `0` in probability.
  have hymean : ∫ ω, yv (X 0 ω) ∂P = p := by
    rw [hE yv]
    simp only [Fin.sum_univ_three, hweProb_zero, hweProb_one, hweProb_two, yv,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  have h2a : TendstoInDistribution (fun N ω => cltY X N ω p) atTop id (fun _ => P)
      (gaussianReal 0 (Var[fun ω => yv (X 0 ω); P]).toNNReal) := by
    have := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun m ω => yv (X m ω))
      HasLaw.id (memLp_comp_of_discrete (hXm 0) yv) (hind yv) (hid yv)
    simp only [hymean] at this
    exact this
  have hlln : ∀ᵐ ω ∂P, Tendsto (fun N => meanY X N ω) atTop (𝓝 p) := by
    have := strong_law_ae_real (fun m ω => yv (X m ω))
      ((memLp_comp_of_discrete (hXm 0) yv).integrable one_le_two)
      (fun i j hij => (hind yv).indepFun hij) (hid yv)
    simp only [hymean] at this
    exact this
  have hmean_meas : ∀ N, AEMeasurable (fun ω => meanY X N ω) P := fun N =>
    (hsum_meas yv N).div_const _
  have hB_meas : ∀ N, AEMeasurable (fun ω => (p - meanY X N ω) / (p * (1 - p))) P := fun N =>
    (aemeasurable_const.sub (hmean_meas N)).div_const _
  have hB : TendstoInMeasure P (fun N ω => (p - meanY X N ω) / (p * (1 - p))) atTop
      (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun N => (hB_meas N).aestronglyMeasurable) ?_
    filter_upwards [hlln] with ω hω
    simpa using ((tendsto_const_nhds (x := p)).sub hω).div_const (p * (1 - p))
  have h2 : TendstoInMeasure P
      (fun N ω => cltY X N ω p * ((p - meanY X N ω) / (p * (1 - p)))) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendstoInDistribution_const
      (P' := gaussianReal 0 (Var[fun ω => yv (X 0 ω); P]).toNNReal) ?_
    exact (h2a.mul_of_tendstoInMeasure_const hB hB_meas).congr
      (fun _ => ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => zero_mul _)
  -- Step 3: `√N F̂ (p̂ q̂) / (p q)` is asymptotically `N(0, 1)`.
  have h3 : TendstoInDistribution (fun N ω => tStat X N ω p) atTop id (fun _ => P)
      (gaussianReal 0 1) := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ h1 ?_ fun N => ?_
    · convert h2 using 1
      funext N ω
      simp [tStat]
    · change AEMeasurable (fun ω => (√N)⁻¹ * ∑ m ∈ range N, wv p (X m ω) / (p * (1 - p)) +
        (√N)⁻¹ * (∑ m ∈ range N, yv (X m ω) - N * p) * ((p - meanY X N ω) / (p * (1 - p)))) P
      exact ((hsum_meas (fun i => wv p i / (p * (1 - p))) N).const_mul _).add
        ((((hsum_meas yv N).sub_const _).const_mul _).mul (hB_meas N))
  -- Step 4: `(p̂ q̂)² / (p q)² → 1` in probability.
  have hV_meas : ∀ N, AEMeasurable (fun ω => vStat X N ω p) P := fun N =>
    (((hmean_meas N).mul (aemeasurable_const.sub (hmean_meas N))).pow_const 2).div_const _
  have hV : TendstoInMeasure P (fun N ω => vStat X N ω p) atTop (fun _ => 1) := by
    refine tendstoInMeasure_of_tendsto_ae (fun N => (hV_meas N).aestronglyMeasurable) ?_
    filter_upwards [hlln] with ω hω
    have := ((hω.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hω)).pow 2).div_const
      ((p * (1 - p)) ^ 2)
    rwa [div_self (pow_pos hr 2).ne'] at this
  -- Step 5: Slutsky, the pathwise identity, and the law of `x²` under `N(0, 1)`.
  have h5 := (h3.continuous_comp (g := fun x : ℝ => x ^ 2)
    (by fun_prop)).div_of_tendstoInMeasure_const one_ne_zero hV hV_meas
  refine (h5.congr (fun N => ae_of_all _ fun ω => ?_) (ae_of_all _ fun x => ?_)).congr_hasLaw
    (Y := fun x : ℝ => x ^ 2) ⟨by fun_prop, gaussianReal_map_sq⟩ hZ
  · exact (hweStat_cellCount_eq X N ω hp0.ne' hq.ne').symm
  · simp

/-- **With `p` known, the Hardy–Weinberg Pearson statistic is asymptotically `χ²₂`.** Under the
hypotheses of `tendstoInDistribution_hweStat`, Pearson's statistic against the *true*
Hardy–Weinberg proportions, `∑ᵢ (nᵢ - N hweProb p i)² / (N hweProb p i)`, converges in
distribution to `χ²₂` (`3` cells, `3 - 1` degrees of freedom; the canonical simple-null
`ProbabilityTheory.tendstoInDistribution_pearsonStatistic`). Estimating `p` by `p̂` lowers the
limit to `χ²₁`. -/
theorem tendstoInDistribution_pearsonStatistic_hweProb
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = hweProb p i) (hp0 : 0 < p) (hp1 : p < 1)
    (hindep : iIndepFun X P) (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 2) P') :
    TendstoInDistribution (fun N ω => pearsonStatistic N (hweProb p) (cellCount X N ω)) atTop Z
      (fun _ => P) P' :=
  tendstoInDistribution_pearsonStatistic hX0 (hweProb_pos hp0 hp1) hindep hident (by simp)
    (by simpa using hZ)

omit [IsProbabilityMeasure P] in
/-- **Monomorphic locus: the statistic is almost surely `0`.** If the allele frequency is `p = 0`
or `p = 1` (Hardy–Weinberg proportions `(1, 0, 0)` or `(0, 0, 1)`), then almost surely every
individual has the same homozygous genotype and the fitted statistic is `0` for every sample
size. -/
theorem hweStat_ae_eq_zero_of_monomorphic [IsFiniteMeasure P]
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = hweProb p i)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P) (hp : p = 0 ∨ p = 1) :
    ∀ᵐ ω ∂P, ∀ N, hweStat N (cellCount X N ω) = 0 := by
  have hXm : ∀ m, AEMeasurable (X m) P := fun m => (hident m).aemeasurable_fst
  -- A genotype class of probability zero is almost surely never observed.
  have hnot : ∀ i, hweProb p i = 0 → ∀ᵐ ω ∂P, ∀ m, X m ω ≠ i := by
    intro i hi
    refine ae_all_iff.2 fun m => ?_
    have h0 : P (X 0 ⁻¹' {i}) = 0 := by
      rw [← measureReal_eq_zero_iff (measure_ne_top _ _), hX0 i, hi]
    have h0' : ∀ᵐ ω ∂P, X 0 ω ≠ i := measure_eq_zero_iff_ae_notMem.1 h0
    exact (hident m).symm.ae_snd (p := fun x => x ≠ i) (measurableSet_singleton i).compl h0'
  have hcount : ∀ ω i, (∀ m, X m ω ≠ i) → ∀ N, cellCount X N ω i = 0 := fun ω i h N =>
    sum_eq_zero fun m _ => ite_eq_right_iff.2 fun hm => absurd hm (h m)
  have hzero : ∀ (ω : Ω) (N : ℕ), cellCount X N ω 1 = 0 →
      (cellCount X N ω 0 = 0 ∨ cellCount X N ω 2 = 0) → hweStat N (cellCount X N ω) = 0 := by
    intro ω N h1 h02
    rw [hweStat_eq_mul_inbreedingHat_sq (cellCount_nonneg X N ω) (sum_cellCount X N ω),
      inbreedingHat, h1]
    rcases h02 with h | h <;> simp [h]
  rcases hp with rfl | rfl
  · filter_upwards [hnot 1 (by simp), hnot 2 (by simp)] with ω h1 h2 N
    exact hzero ω N (hcount ω 1 h1 N) (Or.inr (hcount ω 2 h2 N))
  · filter_upwards [hnot 1 (by simp), hnot 0 (by simp)] with ω h1 h0 N
    exact hzero ω N (hcount ω 1 h1 N) (Or.inl (hcount ω 0 h0 N))

/-- **A monomorphic locus has no `χ²₁` limit.** At `p = 0` or `p = 1` the fitted statistic
converges in distribution to the Dirac mass at `0` (it is almost surely `0`), so it does not
converge to `χ²₁`: the hypothesis `0 < p < 1` of `tendstoInDistribution_hweStat` cannot be
dropped. -/
theorem not_tendstoInDistribution_hweStat_of_monomorphic
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = hweProb p i)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P) (hp : p = 0 ∨ p = 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    ¬ TendstoInDistribution (fun N ω => hweStat N (cellCount X N ω)) atTop Z (fun _ => P) P' := by
  intro h
  have h0 := hweStat_ae_eq_zero_of_monomorphic hX0 hident hp
  have hconst : TendstoInDistribution (fun N ω => hweStat N (cellCount X N ω)) atTop
      (fun _ : Ω => (0 : ℝ)) (fun _ => P) P :=
    (tendstoInDistribution_const (Z := fun _ : Ω => (0 : ℝ)) (l := atTop)
      aemeasurable_const).congr
      (fun N => by filter_upwards [h0] with ω hω using (hω N).symm) (ae_of_all _ fun _ => rfl)
  have huniq := tendstoInDistribution_unique _ h hconst
  rw [hZ.map_eq, Measure.map_const, measure_univ, one_smul] at huniq
  have := congrArg (fun μ : Measure ℝ => μ {0}) huniq
  simp only [chiSquareMeasure_singleton] at this
  simp at this

end Asymptotics

end MathlibExt.Biology.StatisticalGenetics.PearsonLimit
