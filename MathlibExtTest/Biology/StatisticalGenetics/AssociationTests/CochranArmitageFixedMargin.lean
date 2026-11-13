/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.AssociationTests.CochranArmitageFixedMargin
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.UniformOn

/-!
# Tests for the fixed-margin Cochran–Armitage test

* Counting: class counts of a concrete vector, and the number of vectors with prescribed class
  counts computed by enumeration and by `card_classCount_eq_mul_prod_factorial`.
* The multivariate hypergeometric law for a concrete margin: its values, normalization over the
  four possible tables, and its zeros.
* A concrete fixed-margin design: its counts and its statistic.
* Non-vacuity of `measureReal_caseCount_genotypeTotal` on an i.i.d. uniform sample with one case
  and one control, where the margin has positive probability.
* Non-vacuity of `tendstoInDistribution_fmStat`: half cases, half controls, uniform genotypes;
  and `⌊√N⌋` cases, a case fraction tending to `0`.
* Boundary cases: designs without cases or controls, a single-genotype design, and a
  single-genotype population whose statistic has no `χ²₁` limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open MathlibExt.Biology.StatisticalGenetics.CochranArmitageFixedMargin
open MathlibExt.Biology.StatisticalGenetics.CochranArmitage (score)
open MathlibExt.Biology.StatisticalGenetics.GenomicPrediction.ArmitageTrend
open scoped Nat Topology

namespace MathlibExtTest.Biology.StatisticalGenetics.CochranArmitageFixedMargin

/-! ### Counting -/

example : classCount (![0, 1, 1, 2] : Fin 4 → Fin 3) = ![1, 2, 1] := by decide

/-- Three vectors of length `3` over two classes have class counts `(2, 1)`. -/
example : #{v : Fin 3 → Fin 2 | classCount v = ![2, 1]} = 3 := by decide

/-- The same count from `card_classCount_eq_mul_prod_factorial`: `3 · 2! · 1! = 3!`. -/
example : #{v : Fin 3 → Fin 2 | classCount v = ![2, 1]} * ((2)! * (1)!) = 3 ! := by
  simpa [Fin.prod_univ_two] using card_classCount_eq_mul_prod_factorial 3 ![2, 1] (by decide)

/-! ### The multivariate hypergeometric law -/

/-! An urn with genotype margin `n = (1, 2, 1)` (four subjects) and `R = 2` cases. The four
possible case tables have probabilities `1/6, 1/3, 1/6, 1/3`. -/

example : mvHypergeometricReal 2 ![1, 2, 1] ![1, 1, 0] = 1 / 3 := by
  simp [mvHypergeometricReal, Fin.sum_univ_three, Fin.prod_univ_three]
  norm_num [Nat.choose]

example : mvHypergeometricReal 2 ![1, 2, 1] ![1, 0, 1] = 1 / 6 := by
  simp [mvHypergeometricReal, Fin.sum_univ_three, Fin.prod_univ_three]
  norm_num [Nat.choose]

example : mvHypergeometricReal 2 ![1, 2, 1] ![0, 2, 0] = 1 / 6 := by
  simp [mvHypergeometricReal, Fin.sum_univ_three, Fin.prod_univ_three]
  norm_num [Nat.choose]

example : mvHypergeometricReal 2 ![1, 2, 1] ![0, 1, 1] = 1 / 3 := by
  simp [mvHypergeometricReal, Fin.sum_univ_three, Fin.prod_univ_three]
  norm_num [Nat.choose]

/-- The four tables exhaust the conditional law. -/
example : mvHypergeometricReal 2 ![1, 2, 1] ![1, 1, 0] +
    mvHypergeometricReal 2 ![1, 2, 1] ![1, 0, 1] +
    mvHypergeometricReal 2 ![1, 2, 1] ![0, 2, 0] +
    mvHypergeometricReal 2 ![1, 2, 1] ![0, 1, 1] = 1 := by
  simp [mvHypergeometricReal, Fin.sum_univ_three, Fin.prod_univ_three]
  norm_num [Nat.choose]

/-- Case counts not summing to `R` have probability `0`. -/
example : mvHypergeometricReal 2 ![1, 2, 1] ![1, 1, 1] = 0 := by
  simp [mvHypergeometricReal, Fin.sum_univ_three]

/-- Two classes: the hypergeometric law, `C(1,1) C(3,1) / C(4,2) = 1/2`. -/
example : mvHypergeometricReal 2 ![1, 3] ![1, 1] = 1 / 2 := by
  rw [show (![1, 3] : Fin 2 → ℕ) = ![1, 4 - 1] from rfl,
    show (![1, 1] : Fin 2 → ℕ) = ![1, 2 - 1] from rfl,
    mvHypergeometricReal_fin_two (by norm_num) (by norm_num), hypergeometricReal]
  norm_num [Nat.choose]

/-- More cases of a class than its margin: probability `0`. -/
example : mvHypergeometricReal 2 ![1, 2, 1] ![2, 0, 0] = 0 := by
  simp [mvHypergeometricReal, Fin.sum_univ_three, Fin.prod_univ_three]

/-! ### A concrete design -/

/-- Five subjects: cases `0, 1` have classes `2, 1`; controls `2, 3, 4` have classes
`0, 1, 0`. -/
def g5 (k : ℕ) : Fin 3 :=
  match k with
  | 0 => 2
  | 1 => 1
  | 3 => 1
  | _ => 0

theorem caseCount_g5 : caseCount 2 g5 = ![0, 1, 1] := by
  funext i
  fin_cases i <;> decide

theorem controlCount_g5 : controlCount 2 5 g5 = ![2, 1, 0] := by
  funext i
  fin_cases i <;> decide

theorem genotypeTotal_g5 : genotypeTotal 5 g5 = ![2, 2, 1] := by
  funext i
  fin_cases i <;> decide

/-- The statistic of the five-subject design: `N U² / (R S D) = 5 · 7² / (2 · 3 · 14) = 35/12`. -/
example : fmStat 2 5 g5 = 35 / 12 := by
  rw [show (5 : ℕ) = 2 + 3 from rfl, fmStat_eq_of_counts caseCount_g5 genotypeTotal_g5]
  simp [trendStat, total, numer, Fin.sum_univ_three]
  norm_num

/-! ### Boundary cases of the finite statistic -/

example : fmStat 0 5 g5 = 0 := fmStat_zero_cases 5 g5

example : fmStat 5 5 g5 = 0 := fmStat_zero_controls 5 g5

/-- Every subject heterozygous: statistic `0`. -/
example : fmStat 2 5 (fun _ ↦ 1) = 0 := fmStat_eq_zero_of_const (by norm_num) fun _ _ ↦ rfl

/-! ### The populations -/

/-- The concrete `χ²₁` variable: `x ↦ x²` under `N(0, 1)`. -/
theorem hasLaw_sq_chiSquare :
    HasLaw (fun x : ℝ ↦ x ^ 2) (chiSquareMeasure 1) (gaussianReal 0 1) :=
  ⟨by fun_prop, gaussianReal_map_sq⟩

/-- Uniform genotype classes. -/
noncomputable def μG : Measure (Fin 3) := uniformOn Set.univ

instance : IsProbabilityMeasure μG := by unfold μG; infer_instance

theorem μG_real_singleton (g : Fin 3) : μG.real {g} = 1 / 3 := by
  rw [μG, Measure.real, uniformOn_univ]
  simp

/-- The score variance of uniform genotype classes is `(0 + 1 + 4)/3 - 1² = 2/3`. -/
theorem variance_score_μG : Var[score; μG] = 2 / 3 := by
  rw [variance_eq_sub MemLp.of_discrete]
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
  simp only [Pi.pow_apply, μG_real_singleton, Fin.sum_univ_three, score, smul_eq_mul]
  norm_num

/-! ### Non-vacuity of the conditional null law -/

/-- **Non-vacuity of `measureReal_caseCount_genotypeTotal`.** One case (subject `0`) and one
control (subject `1`) with independent uniform genotypes. Given that one subject is in class `0`
and the other in class `1` (an event of probability at least `1/9`), the case is in class `0`
with conditional probability `H = C(1,1) C(1,0) / C(2,1) = 1/2`. -/
theorem exists_conditional_null_law :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → Fin 3),
      (∀ k, HasLaw (G k) μG P) ∧ iIndepFun G P ∧
        1 / 9 ≤ P.real {ω | genotypeTotal 2 (G · ω) = ![1, 1, 0]} ∧
        P.real {ω | caseCount 1 (G · ω) = ![1, 0, 0] ∧ genotypeTotal 2 (G · ω) = ![1, 1, 0]} =
          1 / 2 * P.real {ω | genotypeTotal 2 (G · ω) = ![1, 1, 0]} := by
  obtain ⟨Ω, _, P, G, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ μG
  refine ⟨Ω, _, P, hP, G, hlaw, hindep, ?_, ?_⟩
  · have hsub : {ω | G 0 ω = 0} ∩ {ω | G 1 ω = 1} ⊆
        {ω | genotypeTotal 2 (G · ω) = ![1, 1, 0]} := by
      intro ω ⟨h0, h1⟩
      simp only [Set.mem_ofPred_eq] at h0 h1 ⊢
      funext i
      fin_cases i <;>
        simp only [genotypeTotal, card_filter, sum_range_succ, sum_range_zero, h0, h1] <;> rfl
    have hprod : P.real ({ω | G 0 ω = 0} ∩ {ω | G 1 ω = 1}) = 1 / 9 := by
      have hind := (hindep.indepFun (show (0 : ℕ) ≠ 1 by norm_num)).measure_inter_preimage_eq_mul
        {(0 : Fin 3)} {(1 : Fin 3)} (measurableSet_singleton _) (measurableSet_singleton _)
      have e : ∀ k (g : Fin 3), P.real (G k ⁻¹' {g}) = 1 / 3 := fun k g ↦ by
        rw [← map_measureReal_apply (hmeas k) (measurableSet_singleton g), (hlaw k).map_eq,
          μG_real_singleton]
      rw [show {ω | G 0 ω = 0} ∩ {ω | G 1 ω = 1} = G 0 ⁻¹' {0} ∩ G 1 ⁻¹' {1} from rfl,
        measureReal_def, hind, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, e, e]
      norm_num
    rw [← hprod]
    exact measureReal_mono hsub
  · have h := measureReal_caseCount_genotypeTotal (P := P) 1 1 (G := G)
      (hindep.precomp Fin.val_injective) (πcase := μG) (πctrl := μG)
      (fun k _ ↦ hlaw k) (fun k _ _ ↦ hlaw k) rfl ![1, 0, 0] ![1, 1, 0]
    rw [h]
    congr 1
    simp [mvHypergeometricReal, Fin.sum_univ_three, Fin.prod_univ_three]

/-! ### Non-vacuity of the asymptotic law -/

private theorem tendsto_half : Tendsto (fun N : ℕ ↦ N / 2) atTop atTop :=
  tendsto_atTop_atTop.2 fun b ↦ ⟨2 * b, fun N hN ↦ by omega⟩

private theorem tendsto_sub_half : Tendsto (fun N : ℕ ↦ N - N / 2) atTop atTop :=
  tendsto_atTop_atTop.2 fun b ↦ ⟨2 * b, fun N hN ↦ by omega⟩

/-- **Non-vacuity of `tendstoInDistribution_fmStat`.** The design of size `N` has `⌊N/2⌋` cases
and `N - ⌊N/2⌋` controls, all with independent uniform genotypes (the designs reuse one i.i.d.
sequence). The fixed-margin statistic converges in distribution to `x ↦ x²` under `N(0, 1)`. -/
theorem exists_fmStat_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → Fin 3),
      (∀ k, HasLaw (G k) μG P) ∧ iIndepFun G P ∧
        TendstoInDistribution (fun N ω ↦ fmStat (N / 2) N (G · ω)) atTop (fun x : ℝ ↦ x ^ 2)
          (fun _ ↦ P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, G, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ μG
  refine ⟨Ω, _, P, hP, G, hlaw, hindep, ?_⟩
  exact tendstoInDistribution_fmStat (R := fun N ↦ N / 2) (G := fun _ ↦ G)
    (fun N ↦ Nat.div_le_self N 2) tendsto_half tendsto_sub_half (fun _ k ↦ hmeas k)
    (fun _ ↦ hindep.precomp Fin.val_injective) (πcase := μG) (πctrl := μG)
    (fun _ k _ ↦ hlaw k) (fun _ k _ _ ↦ hlaw k) rfl (by rw [variance_score_μG]; norm_num)
    hasLaw_sq_chiSquare

private theorem tendsto_sqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b ↦ ⟨b * b, fun _ hN ↦ Nat.le_sqrt.2 hN⟩

private theorem tendsto_sub_sqrt : Tendsto (fun N : ℕ ↦ N - Nat.sqrt N) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b ↦ ⟨(b + 1) * (b + 1), fun N hN ↦ ?_⟩
  have h1 : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have h2 : b + 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 hN
  have h3 : Nat.sqrt N * (b + 1) ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul_left _ h2
  have h4 : Nat.sqrt N + b ≤ N := by nlinarith
  omega

/-- **Vanishing case fraction.** With `⌊√N⌋` cases and `N - ⌊√N⌋` controls the case fraction
tends to `0`, and the fixed-margin statistic still converges to `χ²₁`: the theorem needs both
group sizes to grow, not a limiting case fraction. -/
theorem exists_fmStat_tendsto_chiSquare_sqrt :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → Fin 3),
      (∀ k, HasLaw (G k) μG P) ∧ iIndepFun G P ∧
        TendstoInDistribution (fun N ω ↦ fmStat (Nat.sqrt N) N (G · ω)) atTop
          (fun x : ℝ ↦ x ^ 2) (fun _ ↦ P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, G, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ μG
  refine ⟨Ω, _, P, hP, G, hlaw, hindep, ?_⟩
  exact tendstoInDistribution_fmStat (R := Nat.sqrt) (G := fun _ ↦ G)
    (fun N ↦ Nat.sqrt_le_self N) tendsto_sqrt tendsto_sub_sqrt (fun _ k ↦ hmeas k)
    (fun _ ↦ hindep.precomp Fin.val_injective) (πcase := μG) (πctrl := μG)
    (fun _ k _ ↦ hlaw k) (fun _ k _ _ ↦ hlaw k) rfl (by rw [variance_score_μG]; norm_num)
    hasLaw_sq_chiSquare

/-- The case fraction `⌊√N⌋ / N` of that design tends to `0`. -/
example : Tendsto (fun N : ℕ ↦ (Nat.sqrt N : ℝ) / N) atTop (𝓝 0) := by
  have h : ∀ N : ℕ, 1 ≤ N → (Nat.sqrt N : ℝ) / N ≤ 1 / Nat.sqrt N := by
    intro N hN
    have hs : 0 < Nat.sqrt N := Nat.sqrt_pos.2 hN
    have hle : ((Nat.sqrt N * Nat.sqrt N : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sqrt_le N
    push_cast at hle
    rw [div_le_div_iff₀ (by exact_mod_cast hN) (by exact_mod_cast hs)]
    linarith
  have hlim : Tendsto (fun N : ℕ ↦ 1 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_sqrt)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N ↦ by positivity) (eventually_atTop.2 ⟨1, h⟩)

/-! ### Singular genotype law -/

/-- A population where every genotype is class `0`. -/
noncomputable def μG0 : Measure (Fin 3) := Measure.dirac 0

instance : IsProbabilityMeasure μG0 := by unfold μG0; infer_instance

/-- **Singular design, asymptotically.** With every genotype in class `0`, the fixed-margin
statistic does not converge to `χ²₁`, however the group sizes grow. -/
theorem exists_fmStat_not_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → Fin 3),
      (∀ k, HasLaw (G k) μG0 P) ∧ iIndepFun G P ∧
        ¬ TendstoInDistribution (fun N ω ↦ fmStat (N / 2) N (G · ω)) atTop
          (fun x : ℝ ↦ x ^ 2) (fun _ ↦ P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, G, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ μG0
  refine ⟨Ω, _, P, hP, G, hlaw, hindep, ?_⟩
  have hc : ∀ k, ∀ᵐ ω ∂P, G k ω = 0 := fun k ↦ by
    refine (hlaw k).ae_iff (p := fun g : Fin 3 ↦ g = 0) (measurable_of_countable _) |>.2 ?_
    simp [μG0]
  exact not_tendstoInDistribution_fmStat_of_const (R := fun N ↦ N / 2) (G := fun _ ↦ G)
    (fun N ↦ Nat.div_le_self N 2) (fun _ k _ ↦ hc k) hasLaw_sq_chiSquare

end MathlibExtTest.Biology.StatisticalGenetics.CochranArmitageFixedMargin
