/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Multinomial
public import MathlibExt.Probability.Statistics.MultipleTesting.Basic

/-!
# Conditional-binomial exact tests: McNemar and the transmission/disequilibrium test

Several classical exact tests compare two counts `X` and `Y` by conditioning on their total
`X + Y = N`: under the null hypothesis the conditional law of `X` is `Bin(N, 1/2)`, free of
nuisance parameters, and the p-value is the upper tail `P(Bin(N, 1/2) ≥ X)`.

* **McNemar's exact test** (paired binary outcomes). `X` and `Y` count the discordant pairs of
  type `(1, 0)` and `(0, 1)`; the null is marginal homogeneity (the two discordance rates agree),
  and the test conditions on the number of discordant pairs `N = X + Y`.
* **Transmission/disequilibrium test (TDT)** (family trios). `X` and `Y` count the transmissions
  of allele `M` and of the other allele from heterozygous parents to affected offspring; the null
  is no linkage, under which both transmissions are equally likely, and the test conditions on
  the number of informative transmissions `N = X + Y`.

## Setting

* **Conditioning.** On the event `{ω | X ω + Y ω = N}`, through the conditional measure
  `μ[|{ω | X ω + Y ω = N}]`.
* **Null hypothesis.** The *equal-rate Poisson null*: `X ~ Po(r)` and `Y ~ Po(r)` are independent
  with a common unknown rate `r > 0` (the Poissonized two-count model). By
  `ProbabilityTheory.hasLaw_cond_binomial`, given `X + Y = N`, `X ~ Bin(N, 1/2)` for every `r`.
  Results stated with an explicit conditional-law hypothesis cover any other model with this
  conditional law (e.g. a fixed number of pairs with multinomial cell counts).
* **p-value.** `condBinomialPValue N p k = P(Bin(N, p) ≥ k)`, and the test statistic is
  `condBinomialTestPValue X Y ω = condBinomialPValue (X ω + Y ω) (1/2) (X ω)`: one-sided, large
  values of `X` relative to the total are evidence against the null.

## Main results

* `isValidPValue_condBinomialPValue`: if `X ~ Bin(N, p)` under a measure, then the upper tail
  p-value `condBinomialPValue N p ∘ X` is valid (`IsValidPValue`).
* `hasLaw_cond_binomial_half`: under the equal-rate Poisson null, `X ~ Bin(N, 1/2)` given
  `X + Y = N`.
* `isValidPValue_condBinomialTestPValue_cond`: the test is valid conditionally on each total.
* `isValidPValue_condBinomialTestPValue_of_forall_hasLaw`: conditional validity for every total
  gives unconditional validity of the statistic `condBinomialTestPValue X Y`.
* `isValidPValue_condBinomialTestPValue`: unconditional validity under the equal-rate Poisson
  null.
* `mcnemar_isValidPValue`, `tdt_isValidPValue`: the two named instances.

Only the one-sided upper-tail p-value is treated; the lower-tail test is the same statement with
`X` and `Y` swapped. Two-sided variants are not covered.

## References

* Q. McNemar, *Note on the sampling error of the difference between correlated proportions or
  percentages*, Psychometrika 12 (1947), 153–157.
* R. S. Spielman, R. E. McGinnis and W. J. Ewens, *Transmission test for linkage disequilibrium:
  the insulin gene region and insulin-dependent diabetes mellitus (IDDM)*, Am. J. Hum. Genet. 52
  (1993), 506–516.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §4.4–4.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting
open scoped unitInterval NNReal ENNReal

namespace MathlibExt.Probability.Statistics.ExactTests

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **conditional-binomial exact p-value** for an observed count `k` given a total `N`:
the upper-tail probability `P(Bin(N, p) ≥ k)`. McNemar's test and the TDT use `p = 1/2`. -/
noncomputable def condBinomialPValue (N : ℕ) (p : I) (k : ℕ) : ℝ :=
  (binomial N p).real {j | k ≤ j}

/-- The conditional-binomial p-value is antitone in the observed count. -/
theorem condBinomialPValue_antitone (N : ℕ) (p : I) : Antitone (condBinomialPValue N p) :=
  fun _ _ h => measureReal_mono fun _ hj => le_trans h hj

/-- **Validity of the conditional-binomial p-value.** If `X ~ Bin(N, p)` under `μ`, then the
upper-tail p-value `ω ↦ P(Bin(N, p) ≥ X ω)` is valid: `μ {p-value ≤ t} ≤ t` for `t ∈ [0, 1]`.
Applied to a conditional measure `μ[|{X + Y = N}]` this is the conditional validity of the
exact test. -/
theorem isValidPValue_condBinomialPValue {X : Ω → ℕ} {N : ℕ} {p : I}
    (hX : HasLaw X (binomial N p) μ) :
    IsValidPValue μ (fun ω => condBinomialPValue N p (X ω)) := by
  intro s _
  classical
  by_cases hne : ∃ k, condBinomialPValue N p k ≤ s
  · have hset : {ω | condBinomialPValue N p (X ω) ≤ s} = {ω | Nat.find hne ≤ X ω} := by
      ext ω
      exact ⟨fun h => Nat.find_min' hne h,
        fun h => (condBinomialPValue_antitone N p h).trans (Nat.find_spec hne)⟩
    rw [hset, hX.measure_eq (p := (Nat.find hne ≤ ·)) measurableSet_Ici, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (Nat.find_spec hne)
  · have hset : {ω | condBinomialPValue N p (X ω) ≤ s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω h => hne ⟨X ω, h⟩
    simp [hset]

/-- **Null law of the conditional-binomial test.** Under the equal-rate Poisson null
(`X ~ Po(r)`, `Y ~ Po(r)` independent, `r > 0`), given `X + Y = N` the count `X` has law
`Bin(N, 1/2)`, whatever the nuisance rate `r`. -/
theorem hasLaw_cond_binomial_half {X Y : Ω → ℕ} {r : ℝ≥0} (hr : 0 < r) (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure r) μ) (hY : HasLaw Y (poissonMeasure r) μ)
    (hXY : IndepFun X Y μ) (N : ℕ) :
    HasLaw X (binomial N ⟨1 / 2, by norm_num, by norm_num⟩) (μ[|{ω | X ω + Y ω = N}]) := by
  convert hasLaw_cond_binomial (add_pos hr hr) hXm hYm hX hY hXY N using 3
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  refine Subtype.ext ?_
  change (1 / 2 : ℝ) = r / (r + r)
  field_simp
  norm_num

/-- The **conditional-binomial test statistic** for two counts `X` and `Y`: the p-value
`P(Bin(N, 1/2) ≥ X ω)` with `N = X ω + Y ω` the observed total. This is the one-sided (upper)
exact p-value of McNemar's test and of the TDT. -/
noncomputable def condBinomialTestPValue (X Y : Ω → ℕ) (ω : Ω) : ℝ :=
  condBinomialPValue (X ω + Y ω) ⟨1 / 2, by norm_num, by norm_num⟩ (X ω)

/-- **Conditional validity from the conditional law.** If, given the total `X + Y = N`, the count
`X` has law `Bin(N, 1/2)`, then the conditional-binomial test statistic is a valid p-value under
the conditional measure `μ[|{ω | X ω + Y ω = N}]`. -/
theorem isValidPValue_condBinomialTestPValue_cond_of_hasLaw {X Y : Ω → ℕ} {N : ℕ}
    (hS : MeasurableSet {ω | X ω + Y ω = N})
    (hX : HasLaw X (binomial N ⟨1 / 2, by norm_num, by norm_num⟩) (μ[|{ω | X ω + Y ω = N}])) :
    IsValidPValue (μ[|{ω | X ω + Y ω = N}]) (condBinomialTestPValue X Y) := by
  intro s hs
  have h := isValidPValue_condBinomialPValue hX s hs
  have hset : {ω | X ω + Y ω = N} ∩ {ω | condBinomialTestPValue X Y ω ≤ s} =
      {ω | X ω + Y ω = N} ∩
        {ω | condBinomialPValue N ⟨1 / 2, by norm_num, by norm_num⟩ (X ω) ≤ s} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, condBinomialTestPValue]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₁ ▸ h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₁ ▸ h₂⟩⟩
  rwa [cond_apply hS, hset, ← cond_apply hS]

/-- **Conditional validity.** Under the equal-rate Poisson null, the conditional-binomial test
statistic is a valid p-value given each total `X + Y = N`. -/
theorem isValidPValue_condBinomialTestPValue_cond {X Y : Ω → ℕ} {r : ℝ≥0} (hr : 0 < r)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure r) μ)
    (hY : HasLaw Y (poissonMeasure r) μ) (hXY : IndepFun X Y μ) (N : ℕ) :
    IsValidPValue (μ[|{ω | X ω + Y ω = N}]) (condBinomialTestPValue X Y) :=
  isValidPValue_condBinomialTestPValue_cond_of_hasLaw ((hXm.add hYm) (measurableSet_singleton N))
    (hasLaw_cond_binomial_half hr hXm hYm hX hY hXY N)

/-- **From conditional to unconditional validity.** If the counts are measurable and, given each
total `X + Y = N`, `X ~ Bin(N, 1/2)`, then the conditional-binomial test statistic is a valid
p-value under the probability measure `μ`. -/
theorem isValidPValue_condBinomialTestPValue_of_forall_hasLaw [IsProbabilityMeasure μ]
    {X Y : Ω → ℕ} (hXm : Measurable X) (hYm : Measurable Y)
    (hcond : ∀ N, HasLaw X (binomial N ⟨1 / 2, by norm_num, by norm_num⟩)
      (μ[|{ω | X ω + Y ω = N}])) :
    IsValidPValue μ (condBinomialTestPValue X Y) := by
  intro s hs
  set E : ℕ → Set Ω := fun N => {ω | X ω + Y ω = N} with hE
  have hEm : ∀ N, MeasurableSet (E N) := fun N => (hXm.add hYm) (measurableSet_singleton N)
  have hEd : Pairwise (Function.onFun Disjoint E) :=
    fun a b hab => Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
  have hEu : (⋃ N, E N) = Set.univ := Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨_, rfl⟩
  have hterm : ∀ N, μ (E N ∩ {ω | condBinomialTestPValue X Y ω ≤ s}) ≤
      ENNReal.ofReal s * μ (E N) := by
    intro N
    rw [← cond_mul_eq_inter (hEm N)]
    gcongr
    exact isValidPValue_condBinomialTestPValue_cond_of_hasLaw (hEm N) (hcond N) s hs
  calc μ {ω | condBinomialTestPValue X Y ω ≤ s}
      = μ (⋃ N, E N ∩ {ω | condBinomialTestPValue X Y ω ≤ s}) := by
        rw [← Set.iUnion_inter, hEu, Set.univ_inter]
    _ ≤ ∑' N, μ (E N ∩ {ω | condBinomialTestPValue X Y ω ≤ s}) := measure_iUnion_le _
    _ ≤ ∑' N, ENNReal.ofReal s * μ (E N) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal s := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hEd hEm, hEu, measure_univ, mul_one]

/-- **Unconditional validity under the equal-rate Poisson null.** If `X ~ Po(r)` and `Y ~ Po(r)`
are independent with `r > 0`, the conditional-binomial test statistic is a valid p-value under
`μ`, for every value of the nuisance rate `r`. -/
theorem isValidPValue_condBinomialTestPValue {X Y : Ω → ℕ} {r : ℝ≥0} (hr : 0 < r)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure r) μ)
    (hY : HasLaw Y (poissonMeasure r) μ) (hXY : IndepFun X Y μ) :
    IsValidPValue μ (condBinomialTestPValue X Y) :=
  have := hX.isProbabilityMeasure
  isValidPValue_condBinomialTestPValue_of_forall_hasLaw hXm hYm
    (hasLaw_cond_binomial_half hr hXm hYm hX hY hXY)

/-- **McNemar's exact test** (one-sided). For paired binary outcomes, let `B ω` and `C ω` count
the discordant pairs of type `(1, 0)` and `(0, 1)`. In the Poissonized model the counts are
independent, `B ~ Po(λ₁₀)` and `C ~ Po(λ₀₁)`; the null hypothesis of marginal homogeneity is
`λ₁₀ = λ₀₁ = r`. The test conditions on the number of discordant pairs `B + C` and rejects for
large `B`; its p-value `condBinomialTestPValue B C` is valid both given each number of discordant
pairs and unconditionally. -/
theorem mcnemar_isValidPValue {B C : Ω → ℕ} {r : ℝ≥0} (hr : 0 < r) (hBm : Measurable B)
    (hCm : Measurable C) (hB : HasLaw B (poissonMeasure r) μ) (hC : HasLaw C (poissonMeasure r) μ)
    (hBC : IndepFun B C μ) :
    (∀ N, IsValidPValue (μ[|{ω | B ω + C ω = N}]) (condBinomialTestPValue B C)) ∧
      IsValidPValue μ (condBinomialTestPValue B C) :=
  ⟨isValidPValue_condBinomialTestPValue_cond hr hBm hCm hB hC hBC,
    isValidPValue_condBinomialTestPValue hr hBm hCm hB hC hBC⟩

/-- **Transmission/disequilibrium test** (one-sided). From heterozygous parents of affected
offspring, let `T ω` count the transmissions of the marker allele `M` and `U ω` the
transmissions of the other allele. In the Poissonized model the counts are independent,
`T ~ Po(λ_T)` and `U ~ Po(λ_U)`; the null hypothesis of no linkage is `λ_T = λ_U = r` (each
allele is transmitted with probability `1/2`). The test conditions on the number of informative
transmissions `T + U` and rejects for large `T`; its p-value `condBinomialTestPValue T U` is valid
both given each number of informative transmissions and unconditionally. -/
theorem tdt_isValidPValue {T U : Ω → ℕ} {r : ℝ≥0} (hr : 0 < r) (hTm : Measurable T)
    (hUm : Measurable U) (hT : HasLaw T (poissonMeasure r) μ) (hU : HasLaw U (poissonMeasure r) μ)
    (hTU : IndepFun T U μ) :
    (∀ N, IsValidPValue (μ[|{ω | T ω + U ω = N}]) (condBinomialTestPValue T U)) ∧
      IsValidPValue μ (condBinomialTestPValue T U) :=
  mcnemar_isValidPValue hr hTm hUm hT hU hTU

end MathlibExt.Probability.Statistics.ExactTests
