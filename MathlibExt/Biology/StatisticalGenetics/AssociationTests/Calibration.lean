/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.FisherExact
public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg

/-!
# Per-variant calibration of the exact allelic test, and genome-wide pipeline assumptions

## The per-variant test

One biallelic variant in a case–control study. Among the `n₁` alleles carried by cases, `X` are
the tested (risk) allele; among the `n₂` alleles carried by controls, `Y` are. (With `a` cases and
`b` controls, `n₁ = 2a` and `n₂ = 2b`.) The test is the **one-sided exact allelic test**: the
upper Fisher exact p-value of `X` given the allele-count margin `X + Y`, rejecting for an excess
of the tested allele in cases.

**Stated null.** `X ~ Bin(n₁, f)` and `Y ~ Bin(n₂, f)` are independent with a common allele
frequency `0 < f < 1`. Read on individuals, this says the `n₁ + n₂` alleles are independent draws
with the same frequency in cases and controls: no association, unrelated individuals, and
Hardy–Weinberg proportions within each group (allele counting is invalid without HWE; Sasieni
1997). The frequency `f` is a nuisance parameter and is not assumed known.

## What is proved

* `isValidPValue_allelicPValue`: under the stated null the allelic p-value is valid
  (`IsValidPValue`, super-uniform) under the *unconditional* law `μ`, for every `f`. It is
  obtained from the margin-conditional validity of Fisher's test by averaging over the margin
  (`isValidPValue_of_forall_cond`), so it is a statement about one measure, the form a
  genome-wide procedure consumes.
* `cond_allelicPValue_le_upperTail`: calibration in the exact regime. Given the margin
  `X + Y = t`, the p-value is *exactly* calibrated at each attainable level `s = P_H(X ≥ k)`
  (`P(p ≤ s | X + Y = t) = s`) and conservative between attainable levels. The general form for
  any upper-tail p-value is `measure_upperTailPValue_le_upperTail`.

The regime is finite-sample and exact: no asymptotic approximation is used, and none is claimed.
Calibration is *not* exact uniformity. With few copies of the allele the attainable levels are
sparse (for the margin `t = 0`, a monomorphic variant, the p-value is identically `1`), and the
test is strictly conservative there.

## What is *not* claimed

There is no universal GWAS calibration statement. The conclusions above hold only under the
stated per-variant null and its exact finite-sample regime. They fail when that null fails, for
instance under population stratification or a Hardy–Weinberg violation, which make `X` and `Y`
non-binomial or give the groups different frequencies (the test file has a wrong-null example).

Genome-wide validity is a separate matter. `GenomeWideAssumptions` lists exactly what a
downstream Benjamini–Hochberg-type pipeline needs from the vector of per-variant p-values:
measurability, validity of each true-null p-value under one common measure (supplied per variant
by `isValidPValue_allelicPValue`), and one of three dependence hypotheses, `DependenceRegime`:

* `independent`: the p-values are mutually independent (`iIndepFun`). BH at level `q`.
* `prds`: positive regression dependence on the true nulls (`IsPRDSOn`). BH at level `q`.
* `arbitrary`: no dependence hypothesis. BH at level `q` is *not* guaranteed; the pipeline must
  then use Benjamini–Yekutieli (BH at level `q / H_m`).

These are assumptions *for* the pipeline. Nothing here proves that the p-values of variants in
linkage disequilibrium satisfy any of them (such p-values are in general dependent, so
`independent` is not available for them), and nothing here proves FDR control. The FDR
theorems for each regime are
`integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue` (independent),
`integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn` (PRDS) and
`integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence` (BY), in
`MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg`. BY is an optional
downstream composition; this file does not require it.

## Source receipt (reuse search, base `53666a3c1`)

Reused, not redefined: `IsValidPValue` (`MultipleTesting.Basic`); `upperTail`, `upperTailPValue`,
`upperTail_antitone`, `isValidPValue_upperTailPValue` (`ExactTests.TailPValue`);
`fisherUpperPValue`, `isValidPValue_fisherUpper_cond`, `hasLaw_cond_hypergeometric`
(`ExactTests.FisherExact`); `IsPRDSOn` (`MultipleTesting.BenjaminiHochberg`). Not found in the
library and added here: validity of a margin-conditional p-value under the unconditional law,
exact calibration at attainable levels, and the genome-wide assumption bundle. Trend tests,
genomic control and Hardy–Weinberg tests are not defined here.

## Main definitions

* `allelicPValue n₁ n₂ X Y`: the one-sided exact allelic p-value.
* `DependenceRegime`, `DependenceRegime.Holds`: the dependence hypotheses of the pipeline.
* `GenomeWideAssumptions μ p H0 r`: the full hypothesis bundle for a genome-wide BH/BY step.

## Main results

* `measure_upperTailPValue_le_upperTail`, `isValidPValue_of_forall_cond`.
* `isValidPValue_allelicPValue`, `cond_allelicPValue_le_upperTail`,
  `measurable_allelicPValue`.
* `GenomeWideAssumptions.of_allelic`: per-variant allelic nulls give the validity field; the
  dependence field must be supplied.

## References

* P. D. Sasieni, *From genotypes to genes: doubling the sample size*, Biometrics 53 (1997),
  1253–1261.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §3.3 (p-values, Lemma 3.3.1) and §4.5 (Fisher's exact test).
* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and powerful
  approach to multiple testing*, J. R. Statist. Soc. B 57 (1995), 289–300.
* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.ExactTests MathlibExt.Probability.Statistics.MultipleTesting
open scoped unitInterval

namespace MathlibExt.Biology.StatisticalGenetics.AssociationTests.Calibration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Calibration of upper-tail p-values -/

/-- **Exact calibration at attainable levels.** If the count `X` has law `ν` under `μ`, the
upper-tail p-value is exactly calibrated at every attainable level `s = upperTail ν k`:
`μ {upperTailPValue ν X ≤ s} = s`. Between attainable levels it is conservative
(`isValidPValue_upperTailPValue`).

Source: Lehmann–Romano (2005), Lemma 3.3.1. -/
theorem measure_upperTailPValue_le_upperTail {ν : Measure ℕ} [IsProbabilityMeasure ν]
    {X : Ω → ℕ} (hX : HasLaw X ν μ) (k : ℕ) :
    μ {ω | upperTailPValue ν X ω ≤ upperTail ν k} = ENNReal.ofReal (upperTail ν k) := by
  refine le_antisymm
    (isValidPValue_upperTailPValue hX _ ⟨measureReal_nonneg, measureReal_le_one⟩) ?_
  calc ENNReal.ofReal (upperTail ν k) = μ {ω | k ≤ X ω} := by
        rw [hX.measure_eq (p := (k ≤ ·)) (measurableSet_Ici (a := k)), ← ofReal_measureReal]
        rfl
    _ ≤ _ := measure_mono fun ω h => upperTail_antitone ν h

/-- **Validity from conditional validity.** Let `S` be a measurable count that is at most `N`
almost surely, and let `P` agree with `q (S ω)` wherever `S ω ≤ N`. If each `q t` is a valid
p-value conditionally on `S = t` (for `t ≤ N`), then `P` is valid under `μ`.

This is the law of total probability: `μ {P ≤ s} ≤ ∑ₜ μ {S = t} μ[P ≤ s | S = t] ≤ s`. -/
theorem isValidPValue_of_forall_cond [IsProbabilityMeasure μ] {S : Ω → ℕ} (hS : Measurable S)
    {N : ℕ} (hSN : ∀ᵐ ω ∂μ, S ω ≤ N) {P : Ω → ℝ} {q : ℕ → Ω → ℝ}
    (hPq : ∀ ω, S ω ≤ N → P ω = q (S ω) ω)
    (hq : ∀ t ≤ N, IsValidPValue (μ[|S ⁻¹' {t}]) (q t)) : IsValidPValue μ P := by
  intro s hs
  have hsub : {ω | P ω ≤ s} ≤ᵐ[μ]
      (⋃ t ∈ range (N + 1), S ⁻¹' {t} ∩ {ω | q t ω ≤ s} : Set Ω) := by
    filter_upwards [hSN] with ω hω hP
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, mem_range, exists_prop]
    exact ⟨S ω, Nat.lt_succ_of_le hω, rfl, by rwa [← hPq ω hω]⟩
  have hdisj : (range (N + 1) : Set ℕ).PairwiseDisjoint fun t => S ⁻¹' {t} :=
    fun a _ b _ hab => Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
  calc μ {ω | P ω ≤ s}
      ≤ μ (⋃ t ∈ range (N + 1), S ⁻¹' {t} ∩ {ω | q t ω ≤ s}) := measure_mono_ae hsub
    _ ≤ ∑ t ∈ range (N + 1), μ (S ⁻¹' {t} ∩ {ω | q t ω ≤ s}) := measure_biUnion_finset_le _ _
    _ = ∑ t ∈ range (N + 1), μ[{ω | q t ω ≤ s} | S ⁻¹' {t}] * μ (S ⁻¹' {t}) :=
        sum_congr rfl fun t _ => (cond_mul_eq_inter (hS (measurableSet_singleton t)) _ μ).symm
    _ ≤ ∑ t ∈ range (N + 1), ENNReal.ofReal s * μ (S ⁻¹' {t}) := by
        gcongr with t ht
        exact hq t (Nat.lt_succ_iff.1 (mem_range.1 ht)) s hs
    _ = ENNReal.ofReal s * μ (⋃ t ∈ range (N + 1), S ⁻¹' {t}) := by
        rw [← mul_sum, measure_biUnion_finset hdisj fun t _ => hS (measurableSet_singleton t)]
    _ ≤ ENNReal.ofReal s * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal s := mul_one _

/-! ### The exact allelic test -/

/-- The **one-sided exact allelic p-value** of a case–control variant: `X ω` copies of the tested
allele among `n₁` case alleles and `Y ω` among `n₂` control alleles. It is the upper Fisher exact
p-value of `X` given the margin `X + Y`. The margin is capped at `n₁ + n₂`, which changes nothing
under the null (where `X ≤ n₁` and `Y ≤ n₂` almost surely) and makes the definition total. -/
noncomputable def allelicPValue (n₁ n₂ : ℕ) (X Y : Ω → ℕ) (ω : Ω) : ℝ :=
  fisherUpperPValue n₁ n₂ (min (X ω + Y ω) (n₁ + n₂)) (min_le_right _ _) X ω

omit [MeasurableSpace Ω] in
/-- On the event `X + Y = t` with `t ≤ n₁ + n₂`, the allelic p-value is Fisher's p-value with
margin `t`. -/
theorem allelicPValue_eq_fisherUpperPValue {n₁ n₂ t : ℕ} (ht : t ≤ n₁ + n₂) {X Y : Ω → ℕ}
    {ω : Ω} (hω : X ω + Y ω = t) :
    allelicPValue n₁ n₂ X Y ω = fisherUpperPValue n₁ n₂ t ht X ω := by
  subst hω
  simp only [allelicPValue, min_eq_left ht]

/-- The allelic p-value is measurable when the allele counts are. -/
theorem measurable_allelicPValue {n₁ n₂ : ℕ} {X Y : Ω → ℕ} (hXm : Measurable X)
    (hYm : Measurable Y) : Measurable (allelicPValue n₁ n₂ X Y) := by
  have h : allelicPValue n₁ n₂ X Y =
      allelicPValue n₁ n₂ Prod.fst Prod.snd ∘ fun ω => (X ω, Y ω) := rfl
  rw [h]
  exact (measurable_of_countable _).comp (hXm.prodMk hYm)

variable {n₁ n₂ : ℕ} {f : I} {X Y : Ω → ℕ}

/-- **Validity of the exact allelic test.** Under the stated null (`X ~ Bin(n₁, f)` and
`Y ~ Bin(n₂, f)` independent, with common allele frequency `0 < f < 1`), the allelic p-value is
valid under `μ`: `μ {allelicPValue ≤ s} ≤ s` for `s ∈ [0, 1]`, whatever the value of `f`.

This holds only under that null. It is a per-variant statement; it says nothing about the joint
law of the p-values of different variants.

Source: Lehmann–Romano (2005), §4.5 and Lemma 3.3.1. -/
theorem isValidPValue_allelicPValue [IsProbabilityMeasure μ] (hf₀ : 0 < f) (hf₁ : f < 1)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X Bin(n₁, f) μ)
    (hY : HasLaw Y Bin(n₂, f) μ) (hXY : IndepFun X Y μ) :
    IsValidPValue μ (allelicPValue n₁ n₂ X Y) := by
  refine isValidPValue_of_forall_cond (S := fun ω => X ω + Y ω) (hXm.add hYm) (N := n₁ + n₂)
    ?_ (q := fun t => fun ω => if ht : t ≤ n₁ + n₂ then fisherUpperPValue n₁ n₂ t ht X ω else 0)
    (fun ω hω => by simp only [hω, dite_true, allelicPValue_eq_fisherUpperPValue hω rfl])
    (fun t ht => by
      simp only [ht, dite_true]
      exact isValidPValue_fisherUpper_cond hf₀ hf₁ hXm hYm hX hY hXY ht)
  filter_upwards [ae_le_of_hasLaw_binomial hX, ae_le_of_hasLaw_binomial hY] with ω h₁ h₂
  omega

/-- **Calibration of the exact allelic test at attainable levels.** Under the stated null, given
the allele-count margin `X + Y = t ≤ n₁ + n₂`, the allelic p-value is exactly calibrated at each
attainable level `s = P_H(X ≥ k)`, where `H = H(n₁ + n₂, n₁, t)` is the hypergeometric null law:
`P(allelicPValue ≤ s | X + Y = t) = s`. -/
theorem cond_allelicPValue_le_upperTail (hf₀ : 0 < f) (hf₁ : f < 1) (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X Bin(n₁, f) μ) (hY : HasLaw Y Bin(n₂, f) μ)
    (hXY : IndepFun X Y μ) {t : ℕ} (ht : t ≤ n₁ + n₂) (k : ℕ) :
    μ[{ω | allelicPValue n₁ n₂ X Y ω ≤
        upperTail (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).toMeasure k} |
      {ω | X ω + Y ω = t}] =
      ENNReal.ofReal
        (upperTail (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).toMeasure k) := by
  have hmeas : MeasurableSet {ω | X ω + Y ω = t} :=
    (hXm.add hYm) (measurableSet_singleton t)
  have hset : {ω | X ω + Y ω = t} ∩ {ω | allelicPValue n₁ n₂ X Y ω ≤
        upperTail (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).toMeasure k} =
      {ω | X ω + Y ω = t} ∩ {ω | fisherUpperPValue n₁ n₂ t ht X ω ≤
        upperTail (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).toMeasure k} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_right_iff]
    intro hω
    rw [allelicPValue_eq_fisherUpperPValue ht hω]
  rw [cond_apply hmeas, hset, ← cond_apply hmeas]
  exact measure_upperTailPValue_le_upperTail
    (hasLaw_cond_hypergeometric hf₀ hf₁ hXm hYm hX hY hXY ht) k

/-! ### Assumptions for a downstream genome-wide pipeline -/

/-- The dependence hypotheses under which a downstream Benjamini–Hochberg-type step is known to
control the false discovery rate on valid p-values. Choosing a regime is an assumption about the
joint law of the per-variant p-values; it is not derived from the per-variant null. -/
inductive DependenceRegime
  /-- Mutually independent p-values; BH at level `q`. -/
  | independent
  /-- Positive regression dependence on the true nulls (PRDS); BH at level `q`. -/
  | prds
  /-- No assumption on the dependence; the pipeline must use Benjamini–Yekutieli,
  i.e. BH at level `q / H_m`. -/
  | arbitrary

/-- The hypothesis that a dependence regime imposes on the p-value vector `p` with true nulls
`H0`: independence (`iIndepFun`), PRDS on `H0` (`IsPRDSOn`), or nothing. -/
def DependenceRegime.Holds {m : ℕ} (r : DependenceRegime) (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) : Prop :=
  match r with
  | .independent => iIndepFun p μ
  | .prds => IsPRDSOn μ p H0
  | .arbitrary => True

/-- **The hypotheses a genome-wide BH/BY pipeline needs** from `m` per-variant p-values `p` with
(unknown) true-null set `H0`, in dependence regime `r`. They are assumptions for the pipeline,
not proved here: `null_valid` is supplied per variant (for the allelic test by
`isValidPValue_allelicPValue`, only under its stated null); `dependence` must be justified
separately for the variants at hand. -/
structure GenomeWideAssumptions {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) (r : DependenceRegime) : Prop where
  /-- Every p-value is measurable. -/
  measurable : ∀ i, Measurable (p i)
  /-- Every true-null p-value is valid under the one common measure `μ`. -/
  null_valid : ∀ i ∈ H0, IsValidPValue μ (p i)
  /-- The joint law of the p-values satisfies the dependence hypothesis of regime `r`. -/
  dependence : r.Holds μ p H0

/-- **Per-variant allelic nulls supply the validity field.** For `m` variants with allele counts
`X i`, `Y i` from `n₁ i`, `n₂ i` alleles, if each true-null variant satisfies the allelic null
(with its own frequency `f i`) and the p-values satisfy the dependence hypothesis of `r`, the
allelic p-values meet `GenomeWideAssumptions`. The dependence hypothesis is an input. -/
theorem GenomeWideAssumptions.of_allelic {m : ℕ} [IsProbabilityMeasure μ] {n₁ n₂ : Fin m → ℕ}
    {f : Fin m → I} {X Y : Fin m → Ω → ℕ} {H0 : Finset (Fin m)} {r : DependenceRegime}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hnull : ∀ i ∈ H0, 0 < f i ∧ f i < 1 ∧ HasLaw (X i) Bin(n₁ i, f i) μ ∧
      HasLaw (Y i) Bin(n₂ i, f i) μ ∧ IndepFun (X i) (Y i) μ)
    (hdep : r.Holds μ (fun i => allelicPValue (n₁ i) (n₂ i) (X i) (Y i)) H0) :
    GenomeWideAssumptions μ (fun i => allelicPValue (n₁ i) (n₂ i) (X i) (Y i)) H0 r where
  measurable i := measurable_allelicPValue (hXm i) (hYm i)
  null_valid i hi := by
    obtain ⟨hf₀, hf₁, hX, hY, hXY⟩ := hnull i hi
    exact isValidPValue_allelicPValue hf₀ hf₁ (hXm i) (hYm i) hX hY hXY
  dependence := hdep

end MathlibExt.Biology.StatisticalGenetics.AssociationTests.Calibration
