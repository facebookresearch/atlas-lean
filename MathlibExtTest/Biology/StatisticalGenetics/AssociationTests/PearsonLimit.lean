/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.AssociationTests.PearsonLimit
public import MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.UniformOn

/-!
# Tests for Pearson's Hardy–Weinberg `χ²₁` limit

* Hardy–Weinberg proportions at `p = 1/2`, and agreement of `alleleFreqHat` with the pooled
  `MathlibExt.Biology.StatisticalGenetics.GenomicPrediction.ArmitageTrend.alleleFreq`.
* Concrete genotype tables: `X²`, `p̂`, `F̂`, the identity `X² = N F̂²`, and `F̂ = 1 - H_obs / H_exp`.
* A concrete sample of four individuals: its cell counts and fitted statistic.
* Known versus estimated `p` on a table where `p̂ ≠ p`.
* Boundary tables: monomorphic tables (`X² = 0`) and an all-heterozygote table (`F̂ = -1`,
  `X² = N`).
* Non-vacuity of `tendstoInDistribution_hweStat`: an i.i.d. Hardy–Weinberg population at
  `p = 1/2` (two fair alleles) whose fitted statistic converges to `x ↦ x²` under `N(0, 1)`.
* The monomorphic population (`p = 0`) has no `χ²₁` limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open MathlibExt.Biology.StatisticalGenetics.PearsonLimit

namespace MathlibExtTest.Biology.StatisticalGenetics.PearsonLimit

/-! ### Hardy–Weinberg proportions and the allele-frequency estimate -/

example : hweProb (1 / 2) = ![1 / 4, 1 / 2, 1 / 4] := by
  funext i
  fin_cases i <;> simp [hweProb] <;> norm_num

example (p : ℝ) : ∑ i, hweProb p i = 1 := sum_hweProb p

/-- `alleleFreqHat` of the pooled table is the pooled allele frequency of the Cochran–Armitage
development. -/
example (r s : Fin 3 → ℝ) :
    alleleFreqHat (r + s) = MathlibExt.Biology.StatisticalGenetics.GenomicPrediction.ArmitageTrend.alleleFreq r s := by
  simp only [alleleFreqHat, MathlibExt.Biology.StatisticalGenetics.GenomicPrediction.ArmitageTrend.alleleFreq,
    MathlibExt.Biology.StatisticalGenetics.GenomicPrediction.ArmitageTrend.total, Fin.sum_univ_three, Pi.add_apply]
  norm_num

/-! ### Concrete tables -/

/-- Genotype counts `(30, 40, 30)` of `N = 100` individuals. -/
noncomputable def n1 : Fin 3 → ℝ := ![30, 40, 30]

example : alleleFreqHat n1 = 1 / 2 := by
  simp [alleleFreqHat, n1, Fin.sum_univ_three]
  norm_num

/-- Expected counts `(25, 50, 25)`: `X² = 25/25 + 100/50 + 25/25 = 4`. -/
theorem hweStat_n1 : hweStat 100 n1 = 4 := by
  simp [hweStat, pearsonStatistic, alleleFreqHat, hweProb, n1, Fin.sum_univ_three]
  norm_num

example : inbreedingHat n1 = 1 / 5 := by
  simp [inbreedingHat, n1]
  norm_num

/-- `X² = N F̂²` on `n1`: `100 · (1/5)² = 4`. -/
example : hweStat 100 n1 = 100 * (1 / 5 : ℝ) ^ 2 := by
  rw [hweStat_eq_mul_inbreedingHat_sq (fun i => by fin_cases i <;> simp [n1])
    (by simp [n1, Fin.sum_univ_three]; norm_num)]
  simp [inbreedingHat, n1]
  norm_num

/-- `F̂ = 1 - H_obs / H_exp = 1 - 0.4 / 0.5 = 1/5` on `n1`. -/
example : 1 - (n1 1 / ∑ i, n1 i) / (2 * alleleFreqHat n1 * (1 - alleleFreqHat n1)) = 1 / 5 := by
  rw [← inbreedingHat_eq_one_sub (by simp [n1]; norm_num) (by simp [n1]; norm_num)
    (by simp [n1, Fin.sum_univ_three]; norm_num)]
  simp [inbreedingHat, n1]
  norm_num

/-- A table exactly in Hardy–Weinberg proportions has `X² = 0`. -/
example : hweStat 100 ![25, 50, 25] = 0 := by
  simp [hweStat, pearsonStatistic, alleleFreqHat, hweProb, Fin.sum_univ_three]
  norm_num

/-! ### A concrete sample -/

/-- Four individuals with genotype classes `0, 1, 2, 2`; later individuals repeat class `0`. -/
def X4 (m : ℕ) (_ : Unit) : Fin 3 :=
  match m with
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | _ => 0

theorem cellCount_X4 : cellCount X4 4 () = ![1, 1, 2] := by
  funext i
  fin_cases i <;> simp [cellCount, Finset.sum_range_succ, X4]; norm_num

/-- `p̂ = 5/8`, `F̂ = 7/15`, and `X² = 4 · (7/15)² = 196/225`. -/
example : hweStat 4 (cellCount X4 4 ()) = 196 / 225 := by
  rw [cellCount_X4]
  simp [hweStat, pearsonStatistic, alleleFreqHat, hweProb, Fin.sum_univ_three]
  norm_num

/-! ### Known versus estimated allele frequency -/

/-- On the table `(36, 48, 16)` (in Hardy–Weinberg proportions at `p̂ = 2/5`), the fitted
statistic is `0`, while Pearson's statistic against the *known* `p = 1/2` is
`11²/25 + 2²/50 + 9²/25 = 204/25`: estimating `p` absorbs the allele-frequency deviation. -/
example : hweStat 100 ![36, 48, 16] = 0 ∧
    pearsonStatistic 100 (hweProb (1 / 2)) ![36, 48, 16] = 204 / 25 := by
  constructor
  · simp [hweStat, pearsonStatistic, alleleFreqHat, hweProb, Fin.sum_univ_three]
    norm_num
  · simp [pearsonStatistic, hweProb, Fin.sum_univ_three]
    norm_num

/-! ### Boundary tables -/

/-- Monomorphic table (all class `0`): `p̂ = 0`, `X² = 0`. -/
example : hweStat 10 ![10, 0, 0] = 0 := by
  rw [hweStat_eq_mul_inbreedingHat_sq (fun i => by fin_cases i <;> simp)
    (by simp [Fin.sum_univ_three])]
  simp [inbreedingHat]

/-- Monomorphic table (all class `2`): `p̂ = 1`, `X² = 0`. -/
example : hweStat 10 ![0, 0, 10] = 0 := by
  rw [hweStat_eq_mul_inbreedingHat_sq (fun i => by fin_cases i <;> simp)
    (by simp [Fin.sum_univ_three])]
  simp [inbreedingHat]

/-- All heterozygotes: maximal heterozygote excess, `F̂ = -1` and `X² = N = 10`. -/
example : inbreedingHat ![0, 10, 0] = -1 ∧ hweStat 10 ![0, 10, 0] = 10 := by
  constructor
  · simp [inbreedingHat]
    norm_num
  · simp [hweStat, pearsonStatistic, alleleFreqHat, hweProb, Fin.sum_univ_three]
    norm_num

/-! ### The asymptotic law on a concrete population -/

/-- The concrete `χ²₁` variable: `x ↦ x²` under `N(0, 1)`. -/
theorem hasLaw_sq_chiSquare :
    HasLaw (fun x : ℝ => x ^ 2) (chiSquareMeasure 1) (gaussianReal 0 1) :=
  ⟨by fun_prop, gaussianReal_map_sq⟩

/-- The genotype class of an ordered pair of alleles indexed by `Fin 4`: `aa, aA, Aa, AA`. -/
def alleleCount : Fin 4 → Fin 3 := ![0, 1, 1, 2]

/-- Hardy–Weinberg proportions at `p = 1/2`: the genotype class of two independent fair alleles. -/
noncomputable def μH : Measure (Fin 3) := (uniformOn (Set.univ : Set (Fin 4))).map alleleCount

instance : IsProbabilityMeasure μH := by
  unfold μH
  infer_instance

theorem μH_real_singleton (i : Fin 3) : μH.real {i} = hweProb (1 / 2) i := by
  rw [μH, map_measureReal_apply Measurable.of_discrete (measurableSet_singleton i), Measure.real,
    uniformOn_univ]
  have hpre : ∀ j : Fin 3, alleleCount ⁻¹' {j} =
      ((Finset.univ.filter fun x => alleleCount x = j : Finset (Fin 4)) : Set (Fin 4)) := by
    intro j
    ext x
    simp
  have hcard : (Finset.univ.filter fun x : Fin 4 => alleleCount x = i).card = ![1, 2, 1] i := by
    fin_cases i <;> decide
  rw [hpre, Measure.count_apply_finset, hcard]
  fin_cases i <;>
  · simp [hweProb]
    norm_num

/-- **Non-vacuity of `tendstoInDistribution_hweStat`.** For an i.i.d. sample from the
Hardy–Weinberg population at `p = 1/2`, the fitted statistic converges in distribution to
`x ↦ x²` under `N(0, 1)`, i.e. to `χ²₁`. -/
theorem exists_hweStat_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → Fin 3),
      (∀ m, HasLaw (X m) μH P) ∧ iIndepFun X P ∧
        TendstoInDistribution (fun N ω => hweStat N (cellCount X N ω)) atTop
          (fun x : ℝ => x ^ 2) (fun _ => P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, X, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ μH
  refine ⟨Ω, _, P, hP, X, hlaw, hindep, ?_⟩
  have hident : ∀ m, IdentDistrib (X m) (X 0) P P := fun m =>
    ⟨(hmeas m).aemeasurable, (hmeas 0).aemeasurable, (hlaw m).map_eq.trans (hlaw 0).map_eq.symm⟩
  have hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = hweProb (1 / 2) i := fun i => by
    rw [← map_measureReal_apply (hmeas 0) (measurableSet_singleton i), (hlaw 0).map_eq,
      μH_real_singleton]
  exact tendstoInDistribution_hweStat hX0 (by norm_num) (by norm_num) hindep hident
    hasLaw_sq_chiSquare

/-- A monomorphic population: every genotype is class `0` (`p = 0`). -/
noncomputable def μ0 : Measure (Fin 3) := Measure.dirac 0

instance : IsProbabilityMeasure μ0 := by unfold μ0; infer_instance

/-- **Monomorphic locus, asymptotically.** For an i.i.d. sample from the `p = 0` population the
fitted statistic does not converge to `χ²₁`. -/
theorem exists_hweStat_not_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → Fin 3),
      (∀ m, HasLaw (X m) μ0 P) ∧ iIndepFun X P ∧
        ¬ TendstoInDistribution (fun N ω => hweStat N (cellCount X N ω)) atTop
          (fun x : ℝ => x ^ 2) (fun _ => P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, X, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ μ0
  refine ⟨Ω, _, P, hP, X, hlaw, hindep, ?_⟩
  have hident : ∀ m, IdentDistrib (X m) (X 0) P P := fun m =>
    ⟨(hmeas m).aemeasurable, (hmeas 0).aemeasurable, (hlaw m).map_eq.trans (hlaw 0).map_eq.symm⟩
  have hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = hweProb 0 i := fun i => by
    rw [← map_measureReal_apply (hmeas 0) (measurableSet_singleton i), (hlaw 0).map_eq, μ0]
    fin_cases i <;> simp [hweProb]
  exact not_tendstoInDistribution_hweStat_of_monomorphic hX0 hident (Or.inl rfl)
    hasLaw_sq_chiSquare

end MathlibExtTest.Biology.StatisticalGenetics.PearsonLimit
