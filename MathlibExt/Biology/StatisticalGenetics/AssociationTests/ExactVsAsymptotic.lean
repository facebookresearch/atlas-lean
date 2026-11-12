/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.HardyWeinbergExact
public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.UniformOn

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Moments.Basic

/-!
# Exact versus asymptotic Hardy–Weinberg tests, and the limits of genomic control

Among `N` diploid individuals carrying `n_A` copies of allele `A`, the null hypothesis of
Hardy–Weinberg equilibrium (HWE) says that, conditional on `n_A`, the `A` gametes occupy a
uniformly random `n_A`-subset of the `2N` gamete slots. The heterozygote count `n_AB` then has
Levene's law (`MathlibExt.Probability.Statistics.ExactTests.leveneProb`), which involves no
nuisance parameter.

This file compares three ways of turning an observed `n_AB` into a p-value.

1. **Exact test.** Order the possible heterozygote counts by an extremeness key `g` and sum the
   Levene probabilities of the counts at least as extreme as the observed one
   (`orderedPValue`). With `g` the Levene probability itself this is the exact test of
   Wigginton, Cutler and Abecasis (`hweExactPValue`); with `g = id` it is the one-sided test for
   a heterozygote deficit (`hweDeficitPValue`). Both are valid p-values in every finite sample
   with a feasible allele count (`nA ≤ 2 * N`)
   (`isValidPValue_hweExactPValue`, `isValidPValue_hweDeficitPValue`).
2. **Asymptotic test.** Pearson's statistic `X²` (`hweChiSq`) compared with the `χ²₁` law
   (`asymptoticHWEPValue`). Pearson's theorem says `X²` converges in law to `χ²₁` as `N → ∞`
   with the allele frequency fixed in `(0, 1)`, which forces every expected genotype count to
   infinity; the usual finite-sample proxy is Cochran's rule that every expected count is at
   least `5` (`InChiSqRegime`). The limit theorem is **not** formalized here; this file proves
   the failure side. With `N = 10` and `n_A = 2` the expected `AA` count is `0.1`
   (`not_inChiSqRegime_sparse`), the observation of one `AA` homozygote gives `X² = 10`, and
   the asymptotic test at level `0.05` rejects with null probability `1/19 > 0.05`
   (`not_isValidPValue_asymptoticHWEPValue_sparse`), while the exact p-value of the same
   observation is `1/19` (`hweExactPValue_sparse`).
3. **Genomic control.** Dividing the statistic by an inflation factor `λ` before the `χ²₁`
   lookup (`gcPValue`) is valid under an additional model: the null statistic is `λ Z²` with
   `Z ~ N(0, 1)` (`MultiplicativeInflation`, `isValidPValue_gcPValue`). It is not a universal
   repair: in the sparse HWE model above, **no** `λ > 0` makes the scaled p-value valid
   (`not_isValidPValue_gcPValue_sparse`). That failure occurs at the level
   `t = gcPValue λ (10/81)` (about `0.72` at `λ = 1`, tending to `1` as `λ` grows) and comes from
   the discreteness of the null law, as for any non-randomized p-value below `1` on a finite
   support. At the usual level `0.05` the failure is proved only for `λ ∈ (0, 1]`
   (`gcPValue_sparse_rejection_ge`); for large `λ` the level-`0.05` test never
   rejects. Note this range is not the clipped-genomic-control regime: clipping floors the
   factor actually used at `1`, so a clipped factor satisfies `λ ≥ 1`, and `λ < 1` never
   occurs after clipping (dividing by a smaller number inflates the statistic and makes
   rejection easier). The `λ = 1` endpoint is the clipped boundary, and it still rejects with
   null probability at least `1/19`. Genomic control rescales a continuous null law; it
   cannot turn a two-point discrete null law into `χ²₁`.

## Main definitions

* `orderedPValue f g M h`: the mass under `f` of the counts `j < M` with `g j ≤ g h`.
* `leveneMeasure N nA`: Levene's law of the heterozygote count, as a measure on `ℕ`.
* `uniformArrangements N nA`: the uniform law on placements of `nA` alleles in `2N` slots.
* `hweExactPValue`, `hweDeficitPValue`: the two-sided (probability-ordered) and the
  heterozygote-deficit exact p-values.
* `hweChiSq nAA nAB nBB`: Pearson's HWE statistic; `hweChiSqOfHet N nA h` in terms of `h`.
* `chiSqOneSurvival x = P(Z² ≥ x)` for `Z ~ N(0, 1)`; `asymptoticHWEPValue`.
* `InChiSqRegime c nAA nAB nBB`: every expected genotype count is at least `c`.
* `MultiplicativeInflation μ T λ`, `gcPValue λ x`.

## Main results

* `hasLaw_hetCount`: under `uniformArrangements N nA`, `hetCount` has law `leveneMeasure N nA`.
* `isValidPValue_orderedPValue`: any ordered Levene p-value is valid when the count has
  Levene's law; `isValidPValue_hweExactPValue` and `isValidPValue_hweDeficitPValue`.
* `chiSqOneSurvival_le`: the Chernoff bound `P(Z² ≥ x) ≤ 2 e^{-x/2}`.
* `hweChiSq_one_zero`: one `AA` homozygote among `m + 1` individuals with two `A` alleles gives
  `X² = m + 1`, for every `m ≥ 1`.
* `not_isValidPValue_asymptoticHWEPValue_sparse`: the asymptotic p-value is anti-conservative
  in the sparse case.
* `isValidPValue_survival`: for any law `ν` on `ℝ`, `y ↦ ν [y, ∞)` evaluated at a variable with
  law `ν` is a valid p-value.
* `isValidPValue_gcPValue`, `not_isValidPValue_gcPValue_sparse`,
  `gcPValue_sparse_rejection_ge`.

## Reuse receipt (API-00)

Searched `MathlibExt`, `MathlibExtTest`, `WantedExt` and Mathlib for `IsValidPValue`,
`HardyWeinberg`, `leveneProb`, `hetCount`, `FisherExact`, `upperTail`, `genomic control`,
`inflation factor`, `chiSquared`, `survival`, `mgf_gaussianReal`, `measure_ge_le_exp_mul_mgf`.
Reused: `leveneProb`, `hetCount`, `card_hetCount_div_choose`, `sum_leveneProb`
(`ExactTests/HardyWeinbergExact`), `IsValidPValue` (`MultipleTesting/Basic`), and Mathlib's
`gaussianReal`, `mgf_id_gaussianReal`, `measure_ge_le_exp_mul_mgf`, `uniformOn`. Not found, so
defined here: a measure form of Levene's law, a validity theorem for exact HWE p-values, a
chi-square HWE statistic, a validity theorem for survival-function p-values on `ℝ`, and any
genomic-control statement. The `ℕ`-valued `upperTailPValue` of `ExactTests/TailPValue` covers
one-sided orderings only, so the two-sided ordered p-value is proved directly.

## References

* H. Levene, *On a matching problem arising in genetics*, Ann. Math. Statist. 20 (1949),
  91–94.
* J. E. Wigginton, D. J. Cutler and G. R. Abecasis, *A note on exact tests of Hardy–Weinberg
  equilibrium*, Am. J. Hum. Genet. 76 (2005), 887–893.
* J. H. Emigh, *A comparison of tests for Hardy–Weinberg equilibrium*, Biometrics 36 (1980),
  627–642.
* K. Pearson, *On the criterion that a given system of deviations from the probable…*,
  Philos. Mag. (5) 50 (1900), 157–175.
* W. G. Cochran, *Some methods for strengthening the common χ² tests*, Biometrics 10 (1954),
  417–451.
* B. Devlin and K. Roeder, *Genomic control for association studies*, Biometrics 55 (1999),
  997–1004.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  Lemma 3.3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open MathlibExt.Probability.Statistics.ExactTests MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExt.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Exact tests from Levene's law -/

/-- The ordered exact p-value: the mass under `f` of the outcomes `j < M` at least as extreme as
`h`, where `j` is at least as extreme as `h` when `g j ≤ g h`. -/
noncomputable def orderedPValue (f g : ℕ → ℝ) (M h : ℕ) : ℝ :=
  ∑ j ∈ (range M).filter (fun j => g j ≤ g h), f j

/-- **Ordered p-values are super-uniform, combinatorial form.** For a nonnegative mass function
`f`, the `f`-mass of the outcomes whose ordered p-value is at most `t` is at most `t`.

If `h₀` is the least extreme outcome (largest `g`) among those with p-value `≤ t`, every such
outcome is at least as extreme as `h₀`, so their mass is at most the p-value of `h₀`.

Source: Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem sum_filter_orderedPValue_le {f g : ℕ → ℝ} {M : ℕ} (hf : ∀ j, 0 ≤ f j) {t : ℝ}
    (ht : 0 ≤ t) :
    ∑ h ∈ (range M).filter (fun h => orderedPValue f g M h ≤ t), f h ≤ t := by
  set S := (range M).filter (fun h => orderedPValue f g M h ≤ t)
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS, ht]
  obtain ⟨h₀, hh₀, hmax⟩ := S.exists_max_image g hS
  have hsub : S ⊆ (range M).filter (fun j => g j ≤ g h₀) := fun h hh =>
    mem_filter.mpr ⟨(mem_filter.mp hh).1, hmax h hh⟩
  calc ∑ h ∈ S, f h ≤ orderedPValue f g M h₀ :=
        sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hf j
    _ ≤ t := (mem_filter.mp hh₀).2

/-- Levene's probabilities are nonnegative. -/
theorem leveneProb_nonneg (N nA h : ℕ) : 0 ≤ leveneProb N nA h := by
  unfold leveneProb
  split_ifs <;> positivity

/-- More heterozygotes than `A` alleles is impossible. -/
theorem leveneProb_eq_zero_of_lt {N nA h : ℕ} (hh : nA < h) : leveneProb N nA h = 0 := by
  unfold leveneProb
  rw [ite_eq_right_iff]
  intro h
  omega

/-- Levene's law of the heterozygote count given `nA` copies of `A` among `N` individuals, as a
measure on `ℕ` supported on `{0, …, nA}`. -/
noncomputable def leveneMeasure (N nA : ℕ) : Measure ℕ :=
  ∑ j ∈ range (nA + 1), ENNReal.ofReal (leveneProb N nA j) • Measure.dirac j

theorem leveneMeasure_apply (N nA : ℕ) (A : Set ℕ) [DecidablePred (· ∈ A)] :
    leveneMeasure N nA A =
      ENNReal.ofReal (∑ j ∈ (range (nA + 1)).filter (· ∈ A), leveneProb N nA j) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => leveneProb_nonneg N nA j, sum_filter]
  simp only [leveneMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ A <;> simp [hj]

theorem leveneMeasure_singleton (N nA h : ℕ) :
    leveneMeasure N nA {h} = ENNReal.ofReal (leveneProb N nA h) := by
  classical
  rw [leveneMeasure_apply]
  by_cases hh : h ≤ nA
  · have : (range (nA + 1)).filter (· ∈ ({h} : Set ℕ)) = {h} := by
      ext j
      simp only [mem_filter, mem_range, Set.mem_singleton_iff, mem_singleton]
      constructor
      · exact fun hj => hj.2
      · rintro rfl
        exact ⟨by omega, rfl⟩
    rw [this, sum_singleton]
  · have : (range (nA + 1)).filter (· ∈ ({h} : Set ℕ)) = ∅ := by
      ext j
      simp only [mem_filter, mem_range, Set.mem_singleton_iff, notMem_empty, iff_false]
      omega
    rw [this, sum_empty, leveneProb_eq_zero_of_lt (by omega)]

instance (N nA : ℕ) [Fact (nA ≤ 2 * N)] : IsProbabilityMeasure (leveneMeasure N nA) := by
  constructor
  rw [leveneMeasure_apply]
  simp [sum_leveneProb (Fact.out : nA ≤ 2 * N)]

/-- The uniform law on placements of `nA` copies of `A` in the `2N` gamete slots
`Fin N × Fin 2`: the HWE null model conditional on the allele count. -/
noncomputable def uniformArrangements (N nA : ℕ) : Measure (Finset (Fin N × Fin 2)) :=
  uniformOn ((univ.filter fun s : Finset (Fin N × Fin 2) => s.card = nA :
    Finset (Finset (Fin N × Fin 2))) : Set (Finset (Fin N × Fin 2)))

/-- Under the uniform-placement model, the event `{n_AB = h}` has Levene's probability. -/
theorem uniformArrangements_hetCount (N nA h : ℕ) :
    uniformArrangements N nA {s | hetCount s = h} = ENNReal.ofReal (leveneProb N nA h) := by
  classical
  have hset : {s : Finset (Fin N × Fin 2) | hetCount s = h} =
      ((univ.filter fun s : Finset (Fin N × Fin 2) => hetCount s = h :
        Finset (Finset (Fin N × Fin 2))) : Set (Finset (Fin N × Fin 2))) := by
    ext s
    simp
  rw [uniformArrangements, hset, uniformOn_apply_finset, ← filter_and,
    ← card_hetCount_div_choose]
  have hS : (univ.filter fun s : Finset (Fin N × Fin 2) => s.card = nA).card =
      (2 * N).choose nA := by
    simp [card_powersetCard, Nat.mul_comm]
  rw [hS]
  rcases Nat.eq_zero_or_pos ((2 * N).choose nA) with h0 | h0
  · have hz : (univ.filter fun s : Finset (Fin N × Fin 2) =>
        s.card = nA ∧ hetCount s = h).card = 0 := by
      rw [← Nat.le_zero, ← h0, ← hS]
      exact card_le_card fun s hs => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hs).2.1⟩
    simp [hz, h0]
  · rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast h0), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]

/-- **The uniform-placement model realizes Levene's law.** Under `uniformArrangements N nA`,
the heterozygote count has law `leveneMeasure N nA`.

Source: Levene (1949); Wigginton, Cutler and Abecasis (2005). -/
theorem hasLaw_hetCount (N nA : ℕ) :
    HasLaw (hetCount (N := N)) (leveneMeasure N nA) (uniformArrangements N nA) where
  aemeasurable := (Measurable.of_discrete).aemeasurable
  map_eq := by
    refine Measure.ext_of_singleton fun h => ?_
    rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton h),
      leveneMeasure_singleton]
    exact uniformArrangements_hetCount N nA h

/-- **The uniform-placement model is a probability measure for feasible allele counts.**
For `nA ≤ 2 * N` the arrangement set is nonempty, so `uniformArrangements N nA` is a
genuine HWE probability law, not the zero measure. This is proved via `hasLaw_hetCount`:
the pushforward of `uniformArrangements` is Levene's law, which is a probability measure
under the same feasibility hypothesis. -/
instance (N nA : ℕ) [Fact (nA ≤ 2 * N)] :
    IsProbabilityMeasure (uniformArrangements N nA) := by
  constructor
  have hmap := (hasLaw_hetCount N nA).map_eq
  have hlevene : (leveneMeasure N nA) Set.univ = 1 := measure_univ
  have h := congrArg (· Set.univ) hmap
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ,
    hlevene] at h
  exact h

/-- **Validity of ordered exact HWE p-values.** If the heterozygote count `H` has Levene's law,
then for every extremeness key `g` the ordered p-value `orderedPValue (leveneProb N nA) g` at
`H` is a valid p-value. No large-sample approximation is involved.

Source: Wigginton, Cutler and Abecasis (2005); Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem isValidPValue_orderedPValue {H : Ω → ℕ} {N nA : ℕ}
    (hH : HasLaw H (leveneMeasure N nA) μ) (g : ℕ → ℝ) :
    IsValidPValue μ (fun ω => orderedPValue (leveneProb N nA) g (nA + 1) (H ω)) := by
  intro t ht
  rw [hH.measure_eq (p := fun h => orderedPValue (leveneProb N nA) g (nA + 1) h ≤ t)
    MeasurableSet.of_discrete, leveneMeasure_apply]
  exact ENNReal.ofReal_le_ofReal
    (by simpa using sum_filter_orderedPValue_le (leveneProb_nonneg N nA) (g := g) ht.1)

/-- The exact HWE p-value of Wigginton, Cutler and Abecasis: the total Levene probability of the
heterozygote counts that are no more probable than the observed count `h`. -/
noncomputable def hweExactPValue (N nA h : ℕ) : ℝ :=
  orderedPValue (leveneProb N nA) (leveneProb N nA) (nA + 1) h

/-- The one-sided exact p-value for a heterozygote deficit: `P(n_AB ≤ h)` under Levene's law. -/
noncomputable def hweDeficitPValue (N nA h : ℕ) : ℝ :=
  orderedPValue (leveneProb N nA) (fun j => (j : ℝ)) (nA + 1) h

/-- **The exact HWE test is valid in finite samples.** Under the uniform-placement null model
the Wigginton–Cutler–Abecasis p-value of the observed heterozygote count is a valid p-value, for
every `N` and every feasible `nA ≤ 2 * N`. Feasibility is essential: for `nA > 2 * N` the
arrangement set is empty, `uniformArrangements N nA` is the zero measure, and validity
would hold only vacuously, not under an HWE probability law.

Source: Wigginton, Cutler and Abecasis (2005). -/
theorem isValidPValue_hweExactPValue (N nA : ℕ) (_hnA : nA ≤ 2 * N) :
    IsValidPValue (uniformArrangements N nA) (fun s => hweExactPValue N nA (hetCount s)) :=
  isValidPValue_orderedPValue (hasLaw_hetCount N nA) _

/-- **The exact heterozygote-deficit test is valid in finite samples.** As above, this
requires the feasible range `nA ≤ 2 * N`; for `nA > 2 * N` the arrangement set is empty
and the statement would hold only vacuously.

Source: Wigginton, Cutler and Abecasis (2005). -/
theorem isValidPValue_hweDeficitPValue (N nA : ℕ) (_hnA : nA ≤ 2 * N) :
    IsValidPValue (uniformArrangements N nA) (fun s => hweDeficitPValue N nA (hetCount s)) :=
  isValidPValue_orderedPValue (hasLaw_hetCount N nA) _

/-! ### The asymptotic chi-square test and where it fails -/

/-- The estimated frequency `(2 n_AA + n_AB) / (2N)` of allele `A`. -/
noncomputable def freqA (nAA nAB nBB : ℕ) : ℝ :=
  (2 * nAA + nAB : ℝ) / (2 * (nAA + nAB + nBB : ℝ))

/-- Expected `AA` count `N p̂²` under HWE. -/
noncomputable def expectedAA (nAA nAB nBB : ℕ) : ℝ :=
  (nAA + nAB + nBB : ℝ) * freqA nAA nAB nBB ^ 2

/-- Expected `AB` count `2 N p̂ (1 - p̂)` under HWE. -/
noncomputable def expectedAB (nAA nAB nBB : ℕ) : ℝ :=
  2 * (nAA + nAB + nBB : ℝ) * freqA nAA nAB nBB * (1 - freqA nAA nAB nBB)

/-- Expected `BB` count `N (1 - p̂)²` under HWE. -/
noncomputable def expectedBB (nAA nAB nBB : ℕ) : ℝ :=
  (nAA + nAB + nBB : ℝ) * (1 - freqA nAA nAB nBB) ^ 2

/-- Pearson's chi-square statistic for Hardy–Weinberg proportions with the allele frequency
estimated from the sample. -/
noncomputable def hweChiSq (nAA nAB nBB : ℕ) : ℝ :=
  (nAA - expectedAA nAA nAB nBB) ^ 2 / expectedAA nAA nAB nBB +
    (nAB - expectedAB nAA nAB nBB) ^ 2 / expectedAB nAA nAB nBB +
    (nBB - expectedBB nAA nAB nBB) ^ 2 / expectedBB nAA nAB nBB

/-- Pearson's statistic as a function of the heterozygote count `h`, given `N` and `nA`. For
impossible counts (`h > nA` or `nA - h` odd) the natural-number floor division and truncated
subtraction give a meaningless value; those counts have null probability `0`. -/
noncomputable def hweChiSqOfHet (N nA h : ℕ) : ℝ :=
  hweChiSq ((nA - h) / 2) h ((2 * N - nA - h) / 2)

/-- The `χ²₁` survival function `x ↦ P(Z² ≥ x)` for `Z ~ N(0, 1)`. -/
noncomputable def chiSqOneSurvival (x : ℝ) : ℝ :=
  (gaussianReal 0 1).real {z | x ≤ z ^ 2}

/-- The asymptotic HWE p-value: the `χ²₁` tail at Pearson's statistic. -/
noncomputable def asymptoticHWEPValue (N nA h : ℕ) : ℝ :=
  chiSqOneSurvival (hweChiSqOfHet N nA h)

/-- The large-sample regime: every expected genotype count is at least `c`. Pearson's limit
theorem (not formalized here) needs every expected count to grow without bound; Cochran's
finite-sample rule takes `c = 5`. -/
def InChiSqRegime (c : ℝ) (nAA nAB nBB : ℕ) : Prop :=
  c ≤ expectedAA nAA nAB nBB ∧ c ≤ expectedAB nAA nAB nBB ∧ c ≤ expectedBB nAA nAB nBB

theorem chiSqOneSurvival_nonneg (x : ℝ) : 0 ≤ chiSqOneSurvival x := measureReal_nonneg

theorem chiSqOneSurvival_le_one (x : ℝ) : chiSqOneSurvival x ≤ 1 := measureReal_le_one

theorem chiSqOneSurvival_antitone : Antitone chiSqOneSurvival := fun _ _ hxy =>
  measureReal_mono fun _ hz => le_trans hxy hz

/-- **Chernoff bound for `χ²₁`.** `P(Z² ≥ x) ≤ 2 e^{-x/2}` for `x ≥ 0`. -/
theorem chiSqOneSurvival_le {x : ℝ} (hx : 0 ≤ x) : chiSqOneSurvival x ≤ 2 * Real.exp (-x / 2) := by
  set a := √x with ha
  have ha2 : a * a = x := Real.mul_self_sqrt hx
  have hsub : {z : ℝ | x ≤ z ^ 2} ⊆ {z | a ≤ id z} ∪ {z | id z ≤ -a} := by
    intro z hz
    have : a ≤ |z| := by
      rw [ha, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hz
    rcases le_abs'.mp this with h | h
    · exact Or.inr (by simp only [Set.mem_ofPred_eq, id]; linarith)
    · exact Or.inl h
  have hup : (gaussianReal 0 1).real {z | a ≤ id z} ≤ Real.exp (-x / 2) := by
    have := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) a (Real.sqrt_nonneg x)
      (integrable_exp_mul_gaussianReal a)
    rw [mgf_id_gaussianReal, ← Real.exp_add] at this
    refine this.trans_eq (congrArg Real.exp ?_)
    push_cast
    nlinarith
  have hlow : (gaussianReal 0 1).real {z | id z ≤ -a} ≤ Real.exp (-x / 2) := by
    have := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (-a)
      (neg_nonpos.mpr (Real.sqrt_nonneg x)) (integrable_exp_mul_gaussianReal (-a))
    rw [mgf_id_gaussianReal, ← Real.exp_add] at this
    refine this.trans_eq (congrArg Real.exp ?_)
    push_cast
    nlinarith
  calc chiSqOneSurvival x ≤ (gaussianReal 0 1).real ({z | a ≤ id z} ∪ {z | id z ≤ -a}) :=
        measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real {z | a ≤ id z} + (gaussianReal 0 1).real {z | id z ≤ -a} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- `P(Z² ≥ 10) ≤ 0.05`: the asymptotic test rejects `X² ≥ 10` at level `0.05`. -/
theorem chiSqOneSurvival_ten_le : chiSqOneSurvival 10 ≤ 1 / 20 := by
  refine (chiSqOneSurvival_le (by norm_num)).trans ?_
  have he : (2.7182818283 : ℝ) ^ 5 < Real.exp 5 := by
    have h15 : Real.exp 1 ^ 5 = Real.exp 5 := by
      rw [Real.exp_one_pow]
      norm_num
    rw [← h15]
    exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h5 : Real.exp (-10 / 2) = (Real.exp 5)⁻¹ := by
    rw [← Real.exp_neg]
    norm_num
  rw [h5]
  have hpos : 0 < Real.exp 5 := Real.exp_pos 5
  rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

/-- **Sparse-count statistic.** With two `A` alleles carried by a single `AA` homozygote among
`m + 1` individuals (`m ≥ 1`), Pearson's statistic is `X² = m + 1`: it grows linearly in the
sample size, so its `χ²₁` p-value decays like `e^{-(m+1)/2}` (`chiSqOneSurvival_le`), while for
`m = 9` the configuration has Levene probability `1/19` (`leveneProb_sparse_zero`). -/
theorem hweChiSq_one_zero {m : ℕ} (hm : 1 ≤ m) : hweChiSq 1 0 m = m + 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  simp only [hweChiSq, expectedAA, expectedAB, expectedBB, freqA]
  push_cast
  have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℝ) ≠ 0 := by positivity
  have h3 : ((1 : ℝ) + 0 + m) * 2 - (2 + 0) ≠ 0 := by
    intro h
    linarith
  field_simp
  ring

/-- The sparse configuration (`N = 10`, `n_A = 2`, no heterozygote) violates Cochran's
expected-count rule: the expected `AA` count is `0.1`. -/
theorem not_inChiSqRegime_sparse : ¬ InChiSqRegime 5 1 0 9 := by
  rintro ⟨h, -, -⟩
  norm_num [expectedAA, freqA] at h

theorem leveneProb_sparse_zero : leveneProb 10 2 0 = 1 / 19 := by
  norm_num [leveneProb, Nat.factorial]

theorem leveneProb_sparse_one : leveneProb 10 2 1 = 0 := by
  norm_num [leveneProb]

theorem leveneProb_sparse_two : leveneProb 10 2 2 = 18 / 19 := by
  norm_num [leveneProb, Nat.factorial]

theorem hweChiSqOfHet_sparse_zero : hweChiSqOfHet 10 2 0 = 10 := by
  have := hweChiSq_one_zero (m := 9) (by norm_num)
  norm_num [hweChiSqOfHet] at this ⊢
  exact this

theorem hweChiSqOfHet_sparse_two : hweChiSqOfHet 10 2 2 = 10 / 81 := by
  norm_num [hweChiSqOfHet, hweChiSq, expectedAA, expectedAB, expectedBB, freqA]

/-- **The exact p-value of the sparse observation.** One `AA` homozygote and no heterozygote
(`N = 10`, `n_A = 2`) has exact p-value `1/19 ≈ 0.053`: the exact test does not reject at
level `0.05`. -/
theorem hweExactPValue_sparse : hweExactPValue 10 2 0 = 1 / 19 := by
  simp only [hweExactPValue, orderedPValue, sum_filter, sum_range_succ, range_zero, sum_empty,
    leveneProb_sparse_zero, leveneProb_sparse_one, leveneProb_sparse_two]
  norm_num

/-- The asymptotic p-value of the sparse observation is at most `0.05`. -/
theorem asymptoticHWEPValue_sparse_le : asymptoticHWEPValue 10 2 0 ≤ 1 / 20 := by
  rw [asymptoticHWEPValue, hweChiSqOfHet_sparse_zero]
  exact chiSqOneSurvival_ten_le

/-- Under the sparse null model, the event "no heterozygote" has probability `1/19`. -/
theorem uniformArrangements_sparse_zero :
    uniformArrangements 10 2 {s | hetCount s = 0} = ENNReal.ofReal (1 / 19) := by
  rw [uniformArrangements_hetCount, leveneProb_sparse_zero]

/-- **The asymptotic HWE test is anti-conservative for sparse counts.** Under HWE with `N = 10`
individuals and `n_A = 2` copies of `A`, the chi-square p-value is not a valid p-value: the
level-`0.05` asymptotic test rejects with null probability at least `1/19 > 0.05`. The exact
p-value is valid in the same model (`isValidPValue_hweExactPValue`).

Source: Emigh (1980); Wigginton, Cutler and Abecasis (2005). -/
theorem not_isValidPValue_asymptoticHWEPValue_sparse :
    ¬ IsValidPValue (uniformArrangements 10 2)
      (fun s => asymptoticHWEPValue 10 2 (hetCount s)) := by
  intro hv
  have hle := hv (1 / 20) ⟨by norm_num, by norm_num⟩
  have hsub : {s : Finset (Fin 10 × Fin 2) | hetCount s = 0} ⊆
      {s | asymptoticHWEPValue 10 2 (hetCount s) ≤ 1 / 20} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    rw [hs]
    exact asymptoticHWEPValue_sparse_le
  have := (measure_mono hsub).trans hle
  rw [uniformArrangements_sparse_zero, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this

/-! ### Genomic control: valid under multiplicative inflation, not a universal repair -/

/-- **Survival-function p-values are valid.** If `Y` has law `ν` on `ℝ`, then
`ω ↦ ν [Y ω, ∞)` is a valid p-value, whatever `ν` (atoms allowed).

The event `{ν [Y, ∞) ≤ t}` is `{Y ∈ A}` for an upper set `A`; `A` is covered by an increasing
sequence of half-lines `[c n, ∞)` with each `c n ∈ A`, so `ν A ≤ t` by continuity from below.

Source: Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem isValidPValue_survival {ν : Measure ℝ} [IsProbabilityMeasure ν] {Y : Ω → ℝ}
    (hY : HasLaw Y ν μ) : IsValidPValue μ (fun ω => ν.real (Set.Ici (Y ω))) := by
  intro t _
  set S : ℝ → ℝ := fun y => ν.real (Set.Ici y)
  have hS : Antitone S := fun _ _ hxy => measureReal_mono (Set.Ici_subset_Ici.mpr hxy)
  set A := {y | S y ≤ t}
  have hup : ∀ {y z}, y ∈ A → y ≤ z → z ∈ A := fun hy hyz => (hS hyz).trans hy
  have hA : MeasurableSet A := measurableSet_le hS.measurable measurable_const
  rw [hY.measure_eq (p := fun y => S y ≤ t) hA]
  -- `A` covered by `⋃ n, [c n, ∞)` with `c` antitone and `c n ∈ A` gives `ν A ≤ t`.
  have key : ∀ c : ℕ → ℝ, Antitone c → (∀ n, c n ∈ A) → A ⊆ ⋃ n, Set.Ici (c n) →
      ν A ≤ ENNReal.ofReal t := by
    intro c hc hcA hcov
    have hmono : Monotone fun n => Set.Ici (c n) := fun _ _ hmn =>
      Set.Ici_subset_Ici.mpr (hc hmn)
    refine (measure_mono hcov).trans
      (le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun n => ?_)
    change ν (Set.Ici (c n)) ≤ _
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hcA n)
  rcases Set.eq_empty_or_nonempty A with hE | ⟨y₀, hy₀⟩
  · change ν A ≤ _
    rw [hE]
    simp
  by_cases hb : BddBelow A
  · by_cases hm : sInf A ∈ A
    · exact key (fun _ => sInf A) antitone_const (fun _ => hm) fun y hy =>
        Set.mem_iUnion.mpr ⟨0, csInf_le hb hy⟩
    · refine key (fun n => sInf A + 1 / ((n : ℝ) + 1)) (fun m n hmn => ?_) (fun n => ?_)
        fun y hy => ?_
      · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        simp only [add_le_add_iff_left]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      · obtain ⟨z, hz, hzlt⟩ := exists_lt_of_csInf_lt ⟨y₀, hy₀⟩
          (lt_add_of_pos_right (sInf A) (Nat.one_div_pos_of_nat (n := n)))
        exact hup hz hzlt.le
      · have hlt : sInf A < y := lt_of_le_of_ne (csInf_le hb hy) fun h => hm (h ▸ hy)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_Ici]; linarith⟩
  · rw [not_bddBelow_iff] at hb
    refine key (fun n => -(n : ℝ)) (fun m n hmn => ?_) (fun n => ?_) fun y _ => ?_
    · simp only [neg_le_neg_iff, Nat.cast_le]
      exact hmn
    · obtain ⟨z, hz, hzlt⟩ := hb (-(n : ℝ))
      exact hup hz hzlt.le
    · obtain ⟨n, hn⟩ := exists_nat_ge (-y)
      exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_Ici]; linarith⟩

/-- The genomic-control p-value: the `χ²₁` tail at the statistic divided by the inflation
factor `lam` (written `λ` in the literature). -/
noncomputable def gcPValue (lam x : ℝ) : ℝ :=
  chiSqOneSurvival (x / lam)

/-- **The additional model behind genomic control.** Devlin and Roeder's multiplicative
inflation model: under the null, the test statistic is `T = lam · Z²` for a standard normal
`Z`, the same factor `lam` for every marker (e.g. stratification or cryptic relatedness that
scales the variance of an asymptotically normal score). -/
def MultiplicativeInflation (μ : Measure Ω) (T : Ω → ℝ) (lam : ℝ) : Prop :=
  ∃ Z : Ω → ℝ, HasLaw Z (gaussianReal 0 1) μ ∧ ∀ ω, T ω = lam * Z ω ^ 2

/-- **Genomic control is valid under multiplicative inflation.** If the null statistic is
`lam · Z²` with `Z ~ N(0, 1)` and `lam > 0`, then dividing by `lam` restores the `χ²₁` law and
the genomic-control p-value is valid.

Source: Devlin and Roeder (1999). -/
theorem isValidPValue_gcPValue {T : Ω → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hT : MultiplicativeInflation μ T lam) : IsValidPValue μ (fun ω => gcPValue lam (T ω)) := by
  obtain ⟨Z, hZ, hTZ⟩ := hT
  set ν : Measure ℝ := (gaussianReal 0 1).map fun z => z ^ 2
  have hmeas : Measurable fun z : ℝ => z ^ 2 := by fun_prop
  have hsq : HasLaw (fun z : ℝ => z ^ 2) ν (gaussianReal 0 1) := ⟨hmeas.aemeasurable, rfl⟩
  have hY : HasLaw (fun ω => Z ω ^ 2) ν μ := hsq.comp hZ
  have hν : IsProbabilityMeasure ν := hsq.isProbabilityMeasure_iff.mp inferInstance
  have heq : (fun ω => gcPValue lam (T ω)) = fun ω => ν.real (Set.Ici (Z ω ^ 2)) := by
    funext ω
    have hm : ν (Set.Ici (Z ω ^ 2)) = gaussianReal 0 1 {z | Z ω ^ 2 ≤ z ^ 2} := by
      rw [Measure.map_apply hmeas measurableSet_Ici]
      rfl
    rw [gcPValue, hTZ ω, mul_div_cancel_left₀ _ hlam.ne', chiSqOneSurvival, measureReal_def,
      measureReal_def, hm]
  rw [heq]
  exact isValidPValue_survival hY

/-- `P(Z² ≥ x) < 1` for `x > 0`: a standard normal lands in `(-√x, √x)` with positive
probability. -/
theorem chiSqOneSurvival_lt_one {x : ℝ} (hx : 0 < x) : chiSqOneSurvival x < 1 := by
  set s : Set ℝ := {z | x ≤ z ^ 2}
  have hs : MeasurableSet s := measurableSet_le measurable_const (measurable_id.pow_const 2)
  have hsub : Set.Ioo (-√x) √x ⊆ sᶜ := by
    intro z hz
    simp only [s, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    calc z ^ 2 < √x ^ 2 := sq_lt_sq' hz.1 hz.2
      _ = x := Real.sq_sqrt hx.le
  have hvol : volume (Set.Ioo (-√x) √x) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp [Real.sqrt_pos.mpr hx]
  have hpos : (gaussianReal 0 1) sᶜ ≠ 0 := fun h0 =>
    hvol (gaussianReal_absolutelyContinuous' 0 one_ne_zero (measure_mono_null hsub h0))
  have hreal : 0 < (gaussianReal 0 1).real sᶜ :=
    ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have := measureReal_add_measureReal_compl (μ := gaussianReal 0 1) hs
  have hu : (gaussianReal 0 1).real Set.univ = 1 := by simp
  rw [chiSqOneSurvival]
  linarith

/-- **Genomic control is not a universal repair.** In the sparse HWE null model (`N = 10`,
`n_A = 2`) the chi-square statistic takes only the two values `10` and `10/81`, and for every
inflation factor `lam > 0` the genomic-control p-value is still not valid: at the level
`t = gcPValue lam (10/81)`, its own larger value (about `0.72` at `lam = 1`, tending to `1` as
`lam` grows), it rejects with probability one. This failure comes from the discreteness of the
null law, not from genomic control specifically. At the usual level `0.05` the failure is proved
only for `lam ∈ (0, 1]` (`gcPValue_sparse_rejection_ge`); that range includes values below the
clipping floor, so see that theorem for the correct interpretation. -/
theorem not_isValidPValue_gcPValue_sparse {lam : ℝ} (hlam : 0 < lam) :
    ¬ IsValidPValue (uniformArrangements 10 2)
      (fun s => gcPValue lam (hweChiSqOfHet 10 2 (hetCount s))) := by
  intro hv
  set p₂ := gcPValue lam (10 / 81)
  have hp₂ : p₂ < 1 := chiSqOneSurvival_lt_one (by positivity)
  have hle := hv p₂ ⟨chiSqOneSurvival_nonneg _, hp₂.le⟩
  have h0 : {s : Finset (Fin 10 × Fin 2) | hetCount s = 0} ⊆
      {s | gcPValue lam (hweChiSqOfHet 10 2 (hetCount s)) ≤ p₂} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    rw [hs, hweChiSqOfHet_sparse_zero]
    exact chiSqOneSurvival_antitone (div_le_div_of_nonneg_right (by norm_num) hlam.le)
  have h2 : {s : Finset (Fin 10 × Fin 2) | hetCount s = 2} ⊆
      {s | gcPValue lam (hweChiSqOfHet 10 2 (hetCount s)) ≤ p₂} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    rw [hs, hweChiSqOfHet_sparse_two]
  have hdisj : Disjoint {s : Finset (Fin 10 × Fin 2) | hetCount s = 0}
      {s | hetCount s = 2} := by
    rw [Set.disjoint_left]
    intro s h0 h2
    simp only [Set.mem_ofPred_eq] at h0 h2
    omega
  have hunion := measure_union hdisj (measurableSet_singleton 2 |>.preimage
    (Measurable.of_discrete (f := hetCount (N := 10))))
    (μ := uniformArrangements 10 2)
  rw [uniformArrangements_hetCount, uniformArrangements_hetCount, leveneProb_sparse_zero,
    leveneProb_sparse_two, ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hunion
  have hone := (measure_mono (Set.union_subset h0 h2)).trans hle
  rw [hunion] at hone
  have h := (ENNReal.ofReal_le_ofReal_iff (chiSqOneSurvival_nonneg (10 / 81 / lam))).mp hone
  norm_num at h
  exact absurd hp₂ (not_lt.mpr h)

/-- **Genomic control with `lam ≤ 1` leaves the sparse test anti-conservative.** For every
`lam ∈ (0, 1]` the level-`0.05` genomic-control test still rejects with null probability at
least `1/19 > 0.05` in the sparse HWE model. This range is **not** the clipped-genomic-control
regime: clipping floors the factor actually used at `1`, so a clipped factor satisfies
`lam ≥ 1` and `lam < 1` never occurs after clipping (dividing by a smaller number inflates
the statistic and makes rejection easier). The `lam = 1` endpoint is the clipped boundary:
when the estimated inflation is at most `1`, clipping uses `lam = 1`, and the test still
rejects with null probability at least `1/19`. -/
theorem gcPValue_sparse_rejection_ge {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ENNReal.ofReal (1 / 19) ≤ uniformArrangements 10 2
      {s | gcPValue lam (hweChiSqOfHet 10 2 (hetCount s)) ≤ 1 / 20} := by
  rw [← uniformArrangements_sparse_zero]
  refine measure_mono fun s hs => ?_
  simp only [Set.mem_ofPred_eq] at hs ⊢
  rw [hs, hweChiSqOfHet_sparse_zero, gcPValue]
  refine (chiSqOneSurvival_antitone ?_).trans chiSqOneSurvival_ten_le
  rw [le_div_iff₀ hlam]
  nlinarith

end MathlibExt.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic
