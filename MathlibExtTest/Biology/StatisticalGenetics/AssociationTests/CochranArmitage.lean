/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.AssociationTests.CochranArmitage
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.UniformOn

/-!
# Tests for the asymptotic Cochran–Armitage trend test

* A concrete case–control genotype table and its trend statistic.
* A concrete sample of six subjects: the counts, `caStat`, and the `N r²` identity.
* Non-vacuity of `tendstoInDistribution_caStat`: an i.i.d. population with uniform genotype
  classes and a fair case indicator, independent, whose trend statistic converges to the
  concrete `χ²₁` variable `x ↦ x²` under `N(0, 1)`.
* Boundary cases: a small-cell table, tables without cases or controls, a single-genotype
  table, and a single-genotype population whose statistic has no `χ²₁` limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open MathlibExt.Biology.StatisticalGenetics.CochranArmitage
open MathlibExt.Biology.StatisticalGenetics.GenomicPrediction.ArmitageTrend

namespace MathlibExtTest.Biology.StatisticalGenetics.CochranArmitage

/-! ### A concrete genotype table -/

/-- Cases with `0, 1, 2` copies of the counted allele. -/
noncomputable def rC : Fin 3 → ℝ := ![20, 50, 30]

/-- Controls with `0, 1, 2` copies of the counted allele. -/
noncomputable def sC : Fin 3 → ℝ := ![40, 45, 15]

/-- The trend statistic of the `2 × 3` table `rC / sC` (`N = 200`) is `9800 / 831 ≈ 11.79`, to be
referred to `χ²₁`. -/
example : trendStat rC sC = 9800 / 831 := by
  simp [trendStat, total, numer, rC, sC, Fin.sum_univ_three]
  norm_num

/-! ### A concrete sample -/

/-- Six subjects (genotype class, case status); later subjects repeat the first. -/
def S6 (m : ℕ) (_ : Unit) : Fin 3 × Bool :=
  match m with
  | 1 => (1, true)
  | 2 => (2, true)
  | 3 => (1, false)
  | 4 => (2, true)
  | 5 => (2, false)
  | _ => (0, false)

example : caseCount S6 6 () = ![0, 1, 2] := by
  funext i
  fin_cases i <;> simp [caseCount] <;> norm_cast

example : controlCount S6 6 () = ![1, 1, 1] := by
  funext i
  fin_cases i <;> simp [controlCount] <;> norm_cast

/-- The trend statistic of the six-subject sample is `6 / 5`. -/
theorem caStat_S6 : caStat S6 6 () = 6 / 5 := by
  have hr : caseCount S6 6 () = ![0, 1, 2] := by
    funext i
    fin_cases i <;> simp [caseCount] <;> norm_cast
  have hs : controlCount S6 6 () = ![1, 1, 1] := by
    funext i
    fin_cases i <;> simp [controlCount] <;> norm_cast
  simp only [caStat, hr, hs]
  simp [trendStat, total, numer, Fin.sum_univ_three]
  norm_num

/-- `N r² = 6/5` for the six-subject sample, by `caStat_eq_mul_sampleCorrSq`. -/
example : 6 * sampleCorrSq (fun m ↦ score (S6 m ()).1) (fun m ↦ caseInd (S6 m ()).2) 6 =
    6 / 5 := by
  rw [← caStat_S6]
  exact_mod_cast (caStat_eq_mul_sampleCorrSq S6 6 ()).symm

/-! ### The asymptotic law on a concrete population -/

/-- The concrete `χ²₁` variable: `x ↦ x²` under `N(0, 1)`. -/
theorem hasLaw_sq_chiSquare :
    HasLaw (fun x : ℝ ↦ x ^ 2) (chiSquareMeasure 1) (gaussianReal 0 1) :=
  ⟨by fun_prop, gaussianReal_map_sq⟩

/-- Uniform genotype classes. -/
noncomputable def μG : Measure (Fin 3) := uniformOn Set.univ

/-- A fair case indicator. -/
noncomputable def μY : Measure Bool := uniformOn Set.univ

instance : IsProbabilityMeasure μG := by unfold μG; infer_instance
instance : IsProbabilityMeasure μY := by unfold μY; infer_instance

theorem μG_real_singleton (g : Fin 3) : μG.real {g} = 1 / 3 := by
  rw [μG, Measure.real, uniformOn_univ]
  simp

theorem μY_real_singleton (y : Bool) : μY.real {y} = 1 / 2 := by
  rw [μY, Measure.real, uniformOn_univ]
  simp

/-- The score variance of uniform genotype classes is `(0 + 1 + 4)/3 - 1² = 2/3`. -/
theorem variance_score_μG : Var[score; μG] = 2 / 3 := by
  rw [variance_eq_sub MemLp.of_discrete]
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
  simp only [Pi.pow_apply, μG_real_singleton, Fin.sum_univ_three, score, smul_eq_mul]
  norm_num

/-- Laws of a sample `S` from the null population `μG ⊗ μY`. -/
private theorem null_population_facts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : ℕ → Ω → Fin 3 × Bool} (hmeas : ∀ m, Measurable (S m))
    (hlaw : ∀ m, HasLaw (S m) (μG.prod μY) P) :
    (∀ m, IdentDistrib (S m) (S 0) P P) ∧
      IndepFun (fun ω ↦ (S 0 ω).1) (fun ω ↦ (S 0 ω).2) P ∧
      P.real {ω | (S 0 ω).2 = true} = 1 / 2 ∧
      Var[fun ω ↦ score (S 0 ω).1; P] = 2 / 3 := by
  have hmap : P.map (S 0) = μG.prod μY := (hlaw 0).map_eq
  have hfst : P.map (fun ω ↦ (S 0 ω).1) = μG := by
    rw [show (fun ω ↦ (S 0 ω).1) = Prod.fst ∘ S 0 from rfl,
      ← Measure.map_map measurable_fst (hmeas 0), hmap, Measure.map_fst_prod, measure_univ,
      one_smul]
  have hsnd : P.map (fun ω ↦ (S 0 ω).2) = μY := by
    rw [show (fun ω ↦ (S 0 ω).2) = Prod.snd ∘ S 0 from rfl,
      ← Measure.map_map measurable_snd (hmeas 0), hmap, Measure.map_snd_prod, measure_univ,
      one_smul]
  have h1 : Measurable fun ω ↦ (S 0 ω).1 := measurable_fst.comp (hmeas 0)
  have h2 : Measurable fun ω ↦ (S 0 ω).2 := measurable_snd.comp (hmeas 0)
  refine ⟨fun m ↦ ⟨(hmeas m).aemeasurable, (hmeas 0).aemeasurable,
    (hlaw m).map_eq.trans (hlaw 0).map_eq.symm⟩, ?_, ?_, ?_⟩
  · rw [indepFun_iff_map_prod_eq_prod_map_map h1.aemeasurable h2.aemeasurable, hfst, hsnd]
    exact hmap
  · have hset : MeasurableSet {y : Bool | y = true} := measurableSet_singleton true
    rw [show {ω | (S 0 ω).2 = true} = (fun ω ↦ (S 0 ω).2) ⁻¹' {y | y = true} from rfl,
      ← map_measureReal_apply h2 hset, hsnd]
    simpa using μY_real_singleton true
  · rw [← variance_score_μG, ← hfst,
      variance_map (measurable_of_countable score).aemeasurable h1.aemeasurable]
    rfl

/-- **Non-vacuity of `tendstoInDistribution_caStat`.** For an i.i.d. sample from the null
population (uniform genotype classes, independent fair case indicator), the Cochran–Armitage
statistic converges in distribution to `x ↦ x²` under `N(0, 1)`, i.e. to `χ²₁`. -/
theorem exists_caStat_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (S : ℕ → Ω → Fin 3 × Bool),
      (∀ m, HasLaw (S m) (μG.prod μY) P) ∧ iIndepFun S P ∧
        TendstoInDistribution (caStat S) atTop (fun x : ℝ ↦ x ^ 2) (fun _ ↦ P)
          (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, S, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ (μG.prod μY)
  obtain ⟨hident, hnull, hp, hvar⟩ := null_population_facts hmeas hlaw
  refine ⟨Ω, _, P, hP, S, hlaw, hindep, ?_⟩
  exact tendstoInDistribution_caStat (hmeas 0) hindep hident hnull (by rw [hp]; norm_num)
    (by rw [hp]; norm_num) (by rw [hvar]; norm_num) hasLaw_sq_chiSquare

/-! ### Boundary cases -/

/-- **Small cells.** A single case, carrying the only copy-number-`2` genotype among `N = 100`:
the trend statistic is `200 / 11 ≈ 18.2`, far in the `χ²₁` tail, although under the null the
single case is equally likely to be any of the `100` subjects, so a table this extreme has
conditional probability `1 / 100`. The `χ²₁` limit needs every occupied cell to grow. -/
example : trendStat ![0, 0, 1] ![81, 18, 0] = 200 / 11 := by
  simp [trendStat, total, numer, Fin.sum_univ_three]
  norm_num

/-- No cases: the statistic is `0`. -/
example : trendStat 0 ![81, 18, 1] = 0 :=
  trendStat_eq_zero_of_no_cases _ _ (by simp)

/-- No controls: the statistic is `0`. -/
example : trendStat ![81, 18, 1] 0 = 0 :=
  trendStat_eq_zero_of_no_controls _ _ (by simp)

/-- Singular design: everyone is heterozygous, so the score has zero sample variance and the
statistic is `0`, however unbalanced the case counts. -/
example : trendStat ![0, 70, 0] ![0, 5, 0] = 0 :=
  trendStat_eq_zero_of_single_genotype _ _ 1 (fun i hi ↦ by fin_cases i <;> simp_all)
    (fun i hi ↦ by fin_cases i <;> simp_all)

/-- A population where every genotype is class `0`. -/
noncomputable def μG0 : Measure (Fin 3) := Measure.dirac 0

instance : IsProbabilityMeasure μG0 := by unfold μG0; infer_instance

/-- **Singular design, asymptotically.** For an i.i.d. sample from a single-genotype population
the trend statistic does not converge to `χ²₁`. -/
theorem exists_caStat_not_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (S : ℕ → Ω → Fin 3 × Bool),
      (∀ m, HasLaw (S m) (μG0.prod μY) P) ∧ iIndepFun S P ∧
        ¬ TendstoInDistribution (caStat S) atTop (fun x : ℝ ↦ x ^ 2) (fun _ ↦ P)
          (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, S, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ (μG0.prod μY)
  refine ⟨Ω, _, P, hP, S, hlaw, hindep, ?_⟩
  have hident : ∀ m, IdentDistrib (S m) (S 0) P P := fun m ↦
    ⟨(hmeas m).aemeasurable, (hmeas 0).aemeasurable, (hlaw m).map_eq.trans (hlaw 0).map_eq.symm⟩
  have hg : ∀ᵐ ω ∂P, (S 0 ω).1 = 0 := by
    refine (hlaw 0).ae_iff (p := fun x : Fin 3 × Bool ↦ x.1 = 0) (measurable_of_countable _) |>.2 ?_
    refine Measure.quasiMeasurePreserving_fst.ae (p := fun g : Fin 3 ↦ g = 0) ?_
    simp [μG0]
  exact not_tendstoInDistribution_caStat_of_genotype_const hident hg hasLaw_sq_chiSquare

end MathlibExtTest.Biology.StatisticalGenetics.CochranArmitage
