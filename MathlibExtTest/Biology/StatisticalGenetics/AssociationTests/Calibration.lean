/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.AssociationTests.Calibration
public import Mathlib.Probability.IdentDistrib

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.AssociationTests.Calibration`

* Smoke test of the reused API (`IsValidPValue`, `fisherUpperPValue`).
* A concrete variant: 2 cases and 2 controls (`n₁ = n₂ = 4` alleles), margin `t = 3`, observed
  `X = 3`; the allelic p-value is `1/14`, it is valid on the null witness, and it is exactly
  calibrated at the level `1/14` given the margin.
* Boundaries: a monomorphic variant (margin `0`, p-value identically `1`, so uniformity and power
  fail), and a wrong null (a point-mass law of the counts, under which the p-value is
  not valid).
* The genome-wide assumption bundle: built from per-variant nulls, and consumed by the existing
  BH theorems (independent, PRDS) and BY theorem (arbitrary dependence). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.ExactTests MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Biology.StatisticalGenetics.AssociationTests.Calibration
open scoped unitInterval

namespace MathlibExtTest.Biology.StatisticalGenetics.AssociationTests.Calibration

/-! ### Smoke test of the reused API -/

/-- `IsValidPValue` is the repository's super-uniformity predicate. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Ω → ℝ) :
    IsValidPValue μ P ↔ ∀ t ∈ Set.Icc (0 : ℝ) 1, μ {ω | P ω ≤ t} ≤ ENNReal.ofReal t :=
  Iff.rfl

/-- The allelic p-value is Fisher's upper p-value at the observed margin. -/
example {Ω : Type*} (X Y : Ω → ℕ) (ω : Ω) (h : X ω + Y ω = 3) :
    allelicPValue 4 4 X Y ω = fisherUpperPValue 4 4 3 (by norm_num) X ω :=
  allelicPValue_eq_fisherUpperPValue (by norm_num) h

/-! ### A concrete variant -/

/-- Allele frequency `1/2`. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

theorem half_pos : 0 < half := by change (0 : ℝ) < 1 / 2; norm_num

theorem half_lt_one : half < 1 := by change (1 / 2 : ℝ) < 1; norm_num

/-- The null witness: independent case and control allele counts `Bin(n₁, f) ⊗ Bin(n₂, f)`. -/
theorem witness (n₁ n₂ : ℕ) (f : I) :
    HasLaw (fun ω : ℕ × ℕ => ω.1) Bin(n₁, f) (Bin(n₁, f).prod Bin(n₂, f)) ∧
      HasLaw (fun ω : ℕ × ℕ => ω.2) Bin(n₂, f) (Bin(n₁, f).prod Bin(n₂, f)) ∧
      IndepFun (fun ω : ℕ × ℕ => ω.1) (fun ω : ℕ × ℕ => ω.2) (Bin(n₁, f).prod Bin(n₂, f)) :=
  ⟨measurePreserving_fst.hasLaw, measurePreserving_snd.hasLaw,
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id⟩

/-- The hypergeometric upper tail `P_H(X ≥ 3)` for `H(8, 4, 3)` is
`C(4,3) C(4,0) / C(8,3) = 4/56 = 1/14`. -/
theorem upperTail_eight_four_three :
    upperTail (hypergeometric (4 + 4) 4 3 (Nat.le_add_right 4 4) (by norm_num)).toMeasure 3 =
      1 / 14 := by
  have h := fisherUpperPValue_eq_sum (n₁ := 4) (n₂ := 4) (t := 3) (by norm_num)
    (fun _ : Unit => 3) ()
  rw [fisherUpperPValue, upperTailPValue] at h
  rw [h, show Icc 3 3 = ({3} : Finset ℕ) by decide, sum_singleton]
  norm_num [hypergeometricReal, Nat.choose]

/-- **Concrete p-value.** 2 cases and 2 controls (4 alleles each); 3 copies of the tested allele
in total, all 3 in cases. The one-sided exact allelic p-value is `1/14`. -/
example : allelicPValue 4 4 Prod.fst Prod.snd ((3, 0) : ℕ × ℕ) = 1 / 14 := by
  rw [allelicPValue_eq_fisherUpperPValue (t := 3) (by norm_num) rfl, fisherUpperPValue,
    upperTailPValue]
  exact upperTail_eight_four_three

/-- **Validity on the null witness.** With common allele frequency `1/2`, the allelic p-value of
the variant is valid under the unconditional law. -/
theorem valid_witness :
    IsValidPValue (Bin(4, half).prod Bin(4, half)) (allelicPValue 4 4 Prod.fst Prod.snd) :=
  have h := witness 4 4 half
  isValidPValue_allelicPValue half_pos half_lt_one measurable_fst measurable_snd h.1 h.2.1 h.2.2

/-- Validity at the observed level: `P(p ≤ 1/14) ≤ 1/14`. -/
example : (Bin(4, half).prod Bin(4, half)) {ω | allelicPValue 4 4 Prod.fst Prod.snd ω ≤ 1 / 14} ≤
    ENNReal.ofReal (1 / 14) :=
  valid_witness _ ⟨by norm_num, by norm_num⟩

/-- **Exact calibration at the attainable level `1/14`.** Given the margin `X + Y = 3`,
`P(p ≤ 1/14 | X + Y = 3) = 1/14` on the null witness. -/
example : (Bin(4, half).prod Bin(4, half))[{ω | allelicPValue 4 4 Prod.fst Prod.snd ω ≤ 1 / 14} |
    {ω : ℕ × ℕ | ω.1 + ω.2 = 3}] = ENNReal.ofReal (1 / 14) := by
  have h := witness 4 4 half
  have := cond_allelicPValue_le_upperTail half_pos half_lt_one measurable_fst measurable_snd
    h.1 h.2.1 h.2.2 (t := 3) (by norm_num) 3
  rwa [upperTail_eight_four_three] at this

/-! ### Boundary: small counts (calibration is not uniformity) -/

/-- A monomorphic variant (margin `0`) has allelic p-value `1`. -/
theorem allelicPValue_of_monomorphic {Ω : Type*} {n₁ n₂ : ℕ} {X Y : Ω → ℕ} {ω : Ω}
    (h : X ω + Y ω = 0) : allelicPValue n₁ n₂ X Y ω = 1 := by
  have hX : X ω = 0 := by omega
  rw [allelicPValue_eq_fisherUpperPValue (Nat.zero_le _) h, fisherUpperPValue_eq_sum, hX,
    show Icc 0 0 = ({0} : Finset ℕ) by decide, sum_singleton]
  simp [hypergeometricReal]

/-- **Uniformity fails at small counts.** Given a monomorphic margin, `P(p ≤ s | X + Y = 0) = 0`
for every `s < 1`, which is not `s` for `0 < s < 1`: the test is strictly conservative and has no
power there. This holds for any law of the counts, null or not. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n₁ n₂ : ℕ} {X Y : Ω → ℕ}
    (hXm : Measurable X) (hYm : Measurable Y) {s : ℝ} (hs : s < 1) :
    μ[{ω | allelicPValue n₁ n₂ X Y ω ≤ s} | {ω | X ω + Y ω = 0}] = 0 := by
  have hm : MeasurableSet {ω | X ω + Y ω = 0} := (hXm.add hYm) (measurableSet_singleton 0)
  rw [cond_apply hm]
  have : {ω | X ω + Y ω = 0} ∩ {ω | allelicPValue n₁ n₂ X Y ω ≤ s} = ∅ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
      not_le]
    intro h
    rw [allelicPValue_of_monomorphic h]
    exact hs
  rw [this, measure_empty, mul_zero]

/-! ### Boundary: wrong null (validity fails) -/

/-- **Validity fails off the stated null.** With 1 case allele and 1 control allele
(`n₁ = n₂ = 1`) and counts that are deterministically `X = 1`, `Y = 0` (for instance a stratified
sample, or a true association), the allelic p-value is `1/2` with probability one, so
`P(p ≤ 1/2) = 1 > 1/2` and the p-value is not valid. -/
example :
    ¬ IsValidPValue (Measure.dirac ((1, 0) : ℕ × ℕ)) (allelicPValue 1 1 Prod.fst Prod.snd) := by
  have hp : allelicPValue 1 1 Prod.fst Prod.snd ((1, 0) : ℕ × ℕ) = 1 / 2 := by
    rw [allelicPValue_eq_fisherUpperPValue (t := 1) (by norm_num) rfl, fisherUpperPValue_eq_sum,
      show Icc (Prod.fst ((1, 0) : ℕ × ℕ)) 1 = ({1} : Finset ℕ) by decide, sum_singleton]
    norm_num [hypergeometricReal, Nat.choose]
  intro h
  have h' := h (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [Measure.dirac_apply_of_mem (by simp [hp])] at h'
  have : ENNReal.ofReal (1 / 2) < 1 := by
    rw [ENNReal.ofReal_lt_one]; norm_num
  exact absurd h' (not_le.2 this)

/-! ### The genome-wide assumption bundle -/

/-- Two independent null variants on the product of two witnesses. -/
noncomputable abbrev twoVariants : Measure ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (Bin(4, half).prod Bin(4, half)).prod (Bin(4, half).prod Bin(4, half))

/-- The two allele counts of the first variant are independent binomials on `twoVariants`. -/
theorem indep_first : IndepFun (fun ω : (ℕ × ℕ) × (ℕ × ℕ) => ω.1.1) (fun ω => ω.1.2) twoVariants :=
  indepFun_of_identDistrib_pair (witness 4 4 half).2.2
    ⟨by fun_prop, by fun_prop, by simp [Measure.map_fst_prod]⟩

/-- The two allele counts of the second variant are independent binomials on `twoVariants`. -/
theorem indep_second :
    IndepFun (fun ω : (ℕ × ℕ) × (ℕ × ℕ) => ω.2.1) (fun ω => ω.2.2) twoVariants :=
  indepFun_of_identDistrib_pair (witness 4 4 half).2.2
    ⟨by fun_prop, by fun_prop, by simp [Measure.map_snd_prod]⟩

/-- Per-variant allelic nulls give the validity field; the dependence hypothesis of the
`arbitrary` regime is vacuous, so the bundle holds and a downstream pipeline needs a procedure
valid under arbitrary dependence, e.g. BY (BH at level `q / H_m`). -/
example : GenomeWideAssumptions twoVariants
    (fun i => allelicPValue 4 4 (![fun ω => ω.1.1, fun ω => ω.2.1] i)
      (![fun ω => ω.1.2, fun ω => ω.2.2] i)) univ .arbitrary := by
  refine GenomeWideAssumptions.of_allelic (n₁ := fun _ => 4) (n₂ := fun _ => 4)
    (f := fun _ => half) (fun i => ?_) (fun i => ?_) (fun i _ => ?_) trivial
  · fin_cases i
    · exact measurable_fst.fst
    · exact measurable_snd.fst
  · fin_cases i
    · exact measurable_fst.snd
    · exact measurable_snd.snd
  · refine ⟨half_pos, half_lt_one, ?_⟩
    fin_cases i
    · exact ⟨(measurePreserving_fst.comp measurePreserving_fst).hasLaw,
        (measurePreserving_snd.comp measurePreserving_fst).hasLaw, indep_first⟩
    · exact ⟨(measurePreserving_fst.comp measurePreserving_snd).hasLaw,
        (measurePreserving_snd.comp measurePreserving_snd).hasLaw, indep_second⟩

/-- Downstream consumer check: in the `independent` regime the bundle carries exactly the
hypotheses of the existing BH theorem. (The FDR bound is the library theorem, not a new result.) -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ}
    {p : Fin m → Ω → ℝ} {H0 : Finset (Fin m)} (hA : GenomeWideAssumptions μ p H0 .independent)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) ∂μ ≤ q * H0.card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue μ p hA.measurable
    hA.dependence H0 hA.null_valid q hq₀ hq₁

/-- Downstream consumer check, `prds` regime: the bundle feeds the existing PRDS BH theorem. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ}
    {p : Fin m → Ω → ℝ} {H0 : Finset (Fin m)} (hA : GenomeWideAssumptions μ p H0 .prds)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) ∂μ ≤ q * H0.card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn μ p hA.measurable H0
    hA.dependence hA.null_valid q hq₀ hq₁

/-- Downstream consumer check, `arbitrary` regime: the bundle feeds the existing BY theorem
(BH at level `q / H_m`); the dependence field is not used. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ}
    {p : Fin m → Ω → ℝ} {H0 : Finset (Fin m)} (hA : GenomeWideAssumptions μ p H0 .arbitrary)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections (q / harmonic m) fun i => p i ω) ∂μ ≤
      q * H0.card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence μ p hA.measurable H0
    hA.null_valid q hq₀ hq₁

end MathlibExtTest.Biology.StatisticalGenetics.AssociationTests.Calibration
