/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Multinomial
public import MathlibExt.Probability.Statistics.ExactTests.ConditionalBinomial
public import MathlibExt.Probability.Statistics.GLM.CountData.ExactTest

/-!
# Exact one-sided TDT and McNemar p-values

The transmission/disequilibrium test (TDT) of Spielman, McGinnis and Ewens counts, among `d`
transmissions from heterozygous parents, the number `B` that pass on the allele of interest.
Under the null of no linkage, each such transmission is a fair coin, so `B ~ Bin(d, 1/2)` and the
exact one-sided p-value for excess transmission is the binomial upper tail at the observed count.

McNemar's test for paired binary data compares the two discordant counts `X` and `Y`. In the
conditional model where `X` and `Y` are independent Poisson counts with a common rate, given the
number of discordant pairs `X + Y = N`, the count `X` is `Bin(N, 1/2)`, so the same upper tail is
an exact conditional p-value. The TDT has the same form when the transmitted and untransmitted
counts are modeled as independent Poisson counts with equal rates; that is a statistical model
of the counts, not a consequence of Mendelian segregation.

Only one-sided tests (excess transmission, excess of one discordant type) are treated. There are
no chi-square approximations. The p-values are `IsValidPValue`, so they can be passed to the
Bonferroni, Holm and Benjamini–Yekutieli theorems of
`MathlibExt.Probability.Statistics.MultipleTesting` as they are.

## Main definitions

* `fairCoin`: the success probability `1/2`, as an element of `unitInterval`.
* `tdtPValue d B`: the upper tail of `Bin(d, 1/2)` at the observed transmission count.
* `mcnemarPValue N X`: the upper tail of `Bin(N, 1/2)` at the observed discordant count.

## Main results

* `isValidPValue_tdtPValue`: under the null `B ~ Bin(d, 1/2)`, the TDT p-value is valid.
* `hasLaw_cond_binomial_fairCoin`: for independent `X, Y ~ Po(a)`, `X ~ Bin(N, 1/2)` given
  `X + Y = N`.
* `isValidPValue_mcnemarPValue`: the McNemar p-value is valid conditionally on `X + Y = N`.
* `upperTail_binomial_fairCoin`: `P(Bin(d, 1/2) ≥ k) = (∑_{k ≤ j ≤ d} C(d, j)) / 2^d`.

With a random total, `isValidPValue_tdtPValue_total_of_cond` and the two
`isValidPValue_mcnemarPValue_total` variants give unconditional validity.

## References

* R. S. Spielman, R. E. McGinnis and W. J. Ewens, *Transmission test for linkage
  disequilibrium: the insulin gene region and insulin-dependent diabetes mellitus*,
  Am. J. Hum. Genet. 52 (1993), 506–516.
* Q. McNemar, *Note on the sampling error of the difference between correlated proportions or
  percentages*, Psychometrika 12 (1947), 153–157.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §4.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset MathlibExt.Probability.Statistics.ExactTests
open MathlibExt.Probability.Statistics.MultipleTesting
open scoped unitInterval NNReal

namespace MathlibExt.Biology.StatisticalGenetics.TransmissionTest

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The fair-coin success probability `1/2`, as an element of the unit interval. The binomial
null law of the TDT and of McNemar's test is `Bin(n, fairCoin)`. -/
noncomputable def fairCoin : I := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp]
theorem coe_fairCoin : (fairCoin : ℝ) = 1 / 2 := rfl

/-- The exact one-sided TDT p-value. `B ω` is the number of transmissions of the allele of
interest among `d` transmissions from heterozygous parents; the p-value is the probability
`P(Bin(d, 1/2) ≥ B ω)` of at least as many transmissions under the null. -/
noncomputable def tdtPValue (d : ℕ) (B : Ω → ℕ) : Ω → ℝ :=
  upperTailPValue Bin(d, fairCoin) B

/-- **Validity of the one-sided TDT.** If the transmission count `B` has the fair-coin law
`Bin(d, 1/2)` under `μ`, then `μ {tdtPValue d B ≤ s} ≤ s` for every `s ∈ [0, 1]`.

The null law is an explicit hypothesis. Its intended reading is one informative transmission
from each of `d` independent families (heterozygous parent, no linkage). The number `d` of
informative transmissions is fixed, not random. Transmissions to several siblings of one family
are not given a joint law here.

Source: Spielman–McGinnis–Ewens (1993); Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem isValidPValue_tdtPValue {d : ℕ} {B : Ω → ℕ} (hB : HasLaw B Bin(d, fairCoin) μ) :
    IsValidPValue μ (tdtPValue d B) :=
  isValidPValue_upperTailPValue hB

/-- The exact one-sided McNemar p-value. `X ω` is the number of discordant pairs of the first
type among `N` discordant pairs; the p-value is `P(Bin(N, 1/2) ≥ X ω)`. -/
noncomputable def mcnemarPValue (N : ℕ) (X : Ω → ℕ) : Ω → ℝ :=
  upperTailPValue Bin(N, fairCoin) X

/-- The binomial parameter `a / (a + a)` of Poisson conditioning with equal rates is `1/2`. -/
private lemma div_add_self_eq_fairCoin {a : ℝ≥0} (ha : 0 < a) (h : (a : ℝ) / (a + a) ∈ I) :
    (⟨(a : ℝ) / (a + a), h⟩ : I) = fairCoin := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  apply Subtype.ext
  change (a : ℝ) / (a + a) = 1 / 2
  field_simp
  ring

/-- **Poisson conditioning with equal rates.** For independent `X ~ Po(a)` and `Y ~ Po(a)` with
`a > 0`, given `X + Y = N` the count `X` has the fair-coin law `Bin(N, 1/2)`. -/
theorem hasLaw_cond_binomial_fairCoin {X Y : Ω → ℕ} {a : ℝ≥0} (ha : 0 < a)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure a) μ)
    (hY : HasLaw Y (poissonMeasure a) μ) (hXY : IndepFun X Y μ) (N : ℕ) :
    HasLaw X Bin(N, fairCoin) (μ[|{ω | X ω + Y ω = N}]) := by
  convert hasLaw_cond_binomial (add_pos ha ha) hXm hYm hX hY hXY N using 2
  exact (div_add_self_eq_fairCoin ha _).symm

/-- **Validity of the one-sided McNemar test.** Let the discordant counts `X` and `Y` be
independent Poisson counts with a common rate `a > 0`. Conditionally on `X + Y = N`, the McNemar
p-value is valid: `P(mcnemarPValue N X ≤ s | X + Y = N) ≤ s` for `s ∈ [0, 1]`. The bound holds
for every common rate `a`.

The same theorem is the conditional TDT when `X` and `Y` are the transmitted and untransmitted
counts, modeled as independent Poisson counts with equal rates under the null.

Source: McNemar (1947); Lehmann–Romano (2005), §4.6 and Lemma 3.3.1. -/
theorem isValidPValue_mcnemarPValue {X Y : Ω → ℕ} {a : ℝ≥0} (ha : 0 < a)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure a) μ)
    (hY : HasLaw Y (poissonMeasure a) μ) (hXY : IndepFun X Y μ) (N : ℕ) :
    IsValidPValue (μ[|{ω | X ω + Y ω = N}]) (mcnemarPValue N X) :=
  isValidPValue_upperTailPValue (hasLaw_cond_binomial_fairCoin ha hXm hYm hX hY hXY N)

/-- **The fair-coin upper tail.** `P(Bin(d, 1/2) ≥ k) = (∑_{k ≤ j ≤ d} C(d, j)) / 2^d`. -/
theorem upperTail_binomial_fairCoin (d k : ℕ) :
    upperTail Bin(d, fairCoin) k = (∑ j ∈ Icc k d, (d.choose j : ℝ)) / 2 ^ d := by
  have hae : {j | k ≤ j} =ᵐ[Bin(d, fairCoin)] (Icc k d : Set ℕ) := by
    filter_upwards [ae_le_of_hasLaw_binomial (HasLaw.id (μ := Bin(d, fairCoin)))] with j hj
    have hjd : j ≤ d := hj
    simp [hjd]
  rw [upperTail, measureReal_congr hae, ← sum_measureReal_singleton, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ d := (Finset.mem_Icc.1 hj).2
  rw [binomial_real_singleton, coe_fairCoin, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc,
    ← pow_add, Nat.add_sub_cancel' hjd, one_div, inv_pow, div_eq_mul_inv]

end MathlibExt.Biology.StatisticalGenetics.TransmissionTest

/-! ### Tests at the observed total -/

open MathlibExt.Biology.StatisticalGenetics.TransmissionTest

namespace MathlibExt.Probability.Statistics.ExactTests

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **TDT with a random number of informative transmissions.** Let `μ` be a probability measure,
`D ω` the number of informative transmissions (from heterozygous parents), a measurable count, and
`B ω` the number that pass on the allele of interest. If, given each value `D = d` of positive
probability, `B ~ Bin(d, 1/2)` (the null of no linkage, with the transmissions treated as
independent fair coins given `d`), then the TDT p-value evaluated at the observed total,
`ω ↦ P(Bin(D ω, 1/2) ≥ B ω)`, is valid under `μ`. This is the generic averaging lemma
`isValidPValue_of_forall_cond_of_ne_zero` (over the values of `D`) applied to the fixed-`d`
guarantee `isValidPValue_tdtPValue`. -/
theorem isValidPValue_tdtPValue_total_of_cond [IsProbabilityMeasure μ] {D B : Ω → ℕ}
    (hDm : Measurable D)
    (hcond : ∀ d, μ {ω | D ω = d} ≠ 0 → HasLaw B Bin(d, fairCoin) (μ[|{ω | D ω = d}])) :
    IsValidPValue μ (fun ω => tdtPValue (D ω) B ω) :=
  isValidPValue_binomialUpperTail_total_of_cond hDm hcond

/-- **McNemar's test with a random number of discordant pairs.** Let `μ` be a probability measure
and let the measurable counts `X ω` and `Y ω` count the discordant pairs of the two types. If, given
each number `X + Y = N` of discordant pairs of positive probability, `X ~ Bin(N, 1/2)`, then the
McNemar p-value at the observed number of discordant pairs, `ω ↦ P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, is
valid under `μ`.

The conditional law is a hypothesis. The Poissonized model does not need it:
`isValidPValue_mcnemarPValue_total` gets validity there from
`GLM.CountData.isValidPValue_countExactPValue`. In the model with a fixed number of pairs and
multinomial cell counts the conditional law is **not** derived here, and that model is reachable
only through this hypothesis. -/
theorem isValidPValue_mcnemarPValue_total_of_cond [IsProbabilityMeasure μ] {X Y : Ω → ℕ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hcond : ∀ N, μ {ω | X ω + Y ω = N} ≠ 0 →
      HasLaw X Bin(N, fairCoin) (μ[|{ω | X ω + Y ω = N}])) :
    IsValidPValue μ (fun ω => mcnemarPValue (X ω + Y ω) X ω) :=
  isValidPValue_tdtPValue_total_of_cond (D := fun ω => X ω + Y ω) (hXm.add hYm) hcond

/-- **McNemar's test under the equal-rate Poisson null.** Let the measurable discordant counts
`X ~ Po(r)` and `Y ~ Po(r)` be independent with a common rate `r ≥ 0` (the Poissonized null of
marginal homogeneity); `μ` is then a probability measure. Then the McNemar p-value at the observed
number of discordant pairs, `ω ↦ P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, is valid under `μ`, whatever `r`.
The same statement is the TDT when `X` and `Y` are the transmitted and untransmitted counts
*modeled* as independent Poisson counts with equal rates; that is a statistical model of the counts,
not a consequence of Mendelian segregation. This is the merged
`GLM.CountData.isValidPValue_countExactPValue` with library sizes `s₁ = s₂ = 1`, restated for
`mcnemarPValue`. -/
theorem isValidPValue_mcnemarPValue_total {X Y : Ω → ℕ} {r : ℝ≥0} (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure r) μ) (hY : HasLaw Y (poissonMeasure r) μ)
    (hXY : IndepFun X Y μ) :
    IsValidPValue μ (fun ω => mcnemarPValue (X ω + Y ω) X ω) := by
  have := hX.isProbabilityMeasure
  have hfc : GLM.CountData.libraryFraction 1 1 = fairCoin := by
    apply Subtype.ext
    rw [GLM.CountData.coe_libraryFraction, coe_fairCoin]
    norm_num
  have hval := GLM.CountData.isValidPValue_countExactPValue (s₁ := 1) (s₂ := 1) (r := r)
    (by norm_num) hXm hYm (by rwa [one_mul]) (by rwa [one_mul]) hXY
  convert hval using 2 with ω
  rw [GLM.CountData.countExactPValue, GLM.CountData.countExactTail, hfc]
  rfl

end MathlibExt.Probability.Statistics.ExactTests
