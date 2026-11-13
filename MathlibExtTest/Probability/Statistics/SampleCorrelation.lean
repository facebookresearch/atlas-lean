/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SampleCorrelation
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.UniformOn

/-!
# Tests for squared sample correlation asymptotics

* Concrete sample means and squared sample correlations.
* Non-vacuity of `tendstoInDistribution_mul_sampleCorrSq` and
  `tendstoInDistribution_oracleStat`: an i.i.d. sequence of pairs of independent
  fair bits (as reals) has `N r² → χ²₁` in distribution, and so does the oracle
  statistic with known means and variances.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open MathlibExt.Probability.Statistics.SampleCorrelation

namespace MathlibExtTest.Probability.Statistics.SampleCorrelation

/-! ### Concrete sample moments -/

example : sampleMean (fun _ : ℕ ↦ (2 : ℝ)) 5 = 2 := by
  simp [sampleMean]

example : sampleMean (fun m : ℕ ↦ (m : ℝ)) 3 = 1 := by
  simp [sampleMean, Finset.sum_range_succ]
  norm_num

/-- A constant coordinate has zero sample covariance, so `r² = 0`. -/
example : sampleCorrSq (fun _ : ℕ ↦ (1 : ℝ)) (fun m : ℕ ↦ (m : ℝ)) 3 = 0 := by
  simp [sampleCorrSq, sampleMean, Finset.sum_range_succ]

/-- Perfectly correlated samples have `r² = 1`. -/
example : sampleCorrSq (fun m : ℕ ↦ (m : ℝ)) (fun m : ℕ ↦ (m : ℝ)) 3 = 1 := by
  simp [sampleCorrSq, sampleMean, Finset.sum_range_succ]
  norm_num

/-! ### The asymptotic law on a fair-bit population -/

/-- The concrete `χ²₁` variable: `x ↦ x²` under `N(0, 1)`. -/
theorem hasLaw_sq_chiSquare :
    HasLaw (fun x : ℝ ↦ x ^ 2) (chiSquareMeasure 1) (gaussianReal 0 1) :=
  ⟨by fun_prop, gaussianReal_map_sq⟩

/-- A fair bit, as a measure on `Fin 2`. -/
noncomputable def μBit : Measure (Fin 2) := uniformOn Set.univ

instance : IsProbabilityMeasure μBit := by unfold μBit; infer_instance

theorem μBit_real_singleton (g : Fin 2) : μBit.real {g} = 1 / 2 := by
  rw [μBit, Measure.real, uniformOn_univ]
  simp

/-- A fair bit, cast to `ℝ`. -/
def bitCast (g : Fin 2) : ℝ := ((g : ℕ) : ℝ)

/-- The variance of a fair bit is `1 / 4`. -/
theorem variance_bitCast : Var[bitCast; μBit] = 1 / 4 := by
  rw [variance_eq_sub MemLp.of_discrete]
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
  simp only [Pi.pow_apply, μBit_real_singleton, Fin.sum_univ_two, bitCast, smul_eq_mul]
  norm_num

/-- **Non-vacuity of the generic `N r² → χ²₁` theorems.** For an i.i.d. sequence of pairs
of independent fair bits (as reals), both the fitted statistic `N r²` and the oracle
statistic with known means and variances converge in distribution to `χ²₁`. -/
theorem exists_sampleCorrSq_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ × ℝ),
      iIndepFun X P ∧ (∀ m, IdentDistrib (X m) (X 0) P P) ∧
        IndepFun (fun ω ↦ (X 0 ω).1) (fun ω ↦ (X 0 ω).2) P ∧
        MemLp (fun ω ↦ (X 0 ω).1) 2 P ∧ MemLp (fun ω ↦ (X 0 ω).2) 2 P ∧
        TendstoInDistribution
          (fun N ω ↦ N * sampleCorrSq (fun m ↦ (X m ω).1) (fun m ↦ (X m ω).2) N)
          atTop (fun x : ℝ ↦ x ^ 2) (fun _ ↦ P) (gaussianReal 0 1) ∧
        TendstoInDistribution
          (fun (N : ℕ) ω ↦ ((√N)⁻¹ * ∑ m ∈ Finset.range N,
            ((X m ω).1 - ∫ ω, (X 0 ω).1 ∂P) * ((X m ω).2 - ∫ ω, (X 0 ω).2 ∂P)) ^ 2 /
              (Var[fun ω ↦ (X 0 ω).1; P] * Var[fun ω ↦ (X 0 ω).2; P]))
          atTop (fun x : ℝ ↦ x ^ 2) (fun _ ↦ P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, S, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ (μBit.prod μBit)
  have hidentS : ∀ m, IdentDistrib (S m) (S 0) P P := fun m ↦
    ⟨(hmeas m).aemeasurable, (hmeas 0).aemeasurable,
      (hlaw m).map_eq.trans (hlaw 0).map_eq.symm⟩
  have hmap : P.map (S 0) = μBit.prod μBit := (hlaw 0).map_eq
  have hfst : P.map (fun ω ↦ (S 0 ω).1) = μBit := by
    rw [show (fun ω ↦ (S 0 ω).1) = Prod.fst ∘ S 0 from rfl,
      ← Measure.map_map measurable_fst (hmeas 0), hmap, Measure.map_fst_prod, measure_univ,
      one_smul]
  have hsnd : P.map (fun ω ↦ (S 0 ω).2) = μBit := by
    rw [show (fun ω ↦ (S 0 ω).2) = Prod.snd ∘ S 0 from rfl,
      ← Measure.map_map measurable_snd (hmeas 0), hmap, Measure.map_snd_prod, measure_univ,
      one_smul]
  have h1 : Measurable fun ω ↦ (S 0 ω).1 := measurable_fst.comp (hmeas 0)
  have h2 : Measurable fun ω ↦ (S 0 ω).2 := measurable_snd.comp (hmeas 0)
  have hnullS : IndepFun (fun ω ↦ (S 0 ω).1) (fun ω ↦ (S 0 ω).2) P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map h1.aemeasurable h2.aemeasurable, hfst, hsnd]
    exact hmap
  have hvarA : Var[fun ω ↦ bitCast (S 0 ω).1; P] = 1 / 4 := by
    rw [← variance_bitCast, ← hfst,
      variance_map (measurable_of_countable bitCast).aemeasurable h1.aemeasurable]
    rfl
  have hvarB : Var[fun ω ↦ bitCast (S 0 ω).2; P] = 1 / 4 := by
    rw [← variance_bitCast, ← hsnd,
      variance_map (measurable_of_countable bitCast).aemeasurable h2.aemeasurable]
    rfl
  have hA : MemLp (fun ω ↦ bitCast (S 0 ω).1) 2 P := by
    refine memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ fun ω ↦ ?_)
      ((measurable_of_countable bitCast).comp h1).aestronglyMeasurable 2
    simp only [Function.comp_apply, bitCast, Set.mem_Icc]
    have hlt := (S 0 ω).1.isLt
    constructor
    · positivity
    · exact_mod_cast Nat.le_of_lt_succ hlt
  have hB : MemLp (fun ω ↦ bitCast (S 0 ω).2) 2 P := by
    refine memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ fun ω ↦ ?_)
      ((measurable_of_countable bitCast).comp h2).aestronglyMeasurable 2
    simp only [Function.comp_apply, bitCast, Set.mem_Icc]
    have hlt := (S 0 ω).2.isLt
    constructor
    · positivity
    · exact_mod_cast Nat.le_of_lt_succ hlt
  refine ⟨Ω, _, P, hP, fun m ω ↦ (bitCast (S m ω).1, bitCast (S m ω).2), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact hindep.comp (fun _ ↦ fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2))
      fun _ ↦ measurable_of_countable _
  · exact fun m ↦ (hidentS m).comp
      (measurable_of_countable (fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2)))
  · exact hnullS.comp (φ := bitCast) (ψ := bitCast) (measurable_of_countable _)
      (measurable_of_countable _)
  · exact hA
  · exact hB
  · have hvarA' : Var[fun ω ↦
        (((fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2)) ∘ S 0) ω).1; P] = 1 / 4 :=
      hvarA
    have hvarB' : Var[fun ω ↦
        (((fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2)) ∘ S 0) ω).2; P] = 1 / 4 :=
      hvarB
    exact tendstoInDistribution_mul_sampleCorrSq
      (hindep.comp (fun _ ↦ fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2))
        fun _ ↦ measurable_of_countable _)
      (fun m ↦ (hidentS m).comp
        (measurable_of_countable (fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2))))
      (hnullS.comp (φ := bitCast) (ψ := bitCast) (measurable_of_countable _)
        (measurable_of_countable _))
      hA hB (by rw [hvarA']; norm_num) (by rw [hvarB']; norm_num) hasLaw_sq_chiSquare
  · have hvarA' : Var[fun ω ↦
        (((fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2)) ∘ S 0) ω).1; P] = 1 / 4 :=
      hvarA
    have hvarB' : Var[fun ω ↦
        (((fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2)) ∘ S 0) ω).2; P] = 1 / 4 :=
      hvarB
    exact tendstoInDistribution_oracleStat
      (hindep.comp (fun _ ↦ fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2))
        fun _ ↦ measurable_of_countable _)
      (fun m ↦ (hidentS m).comp
        (measurable_of_countable (fun x : Fin 2 × Fin 2 ↦ (bitCast x.1, bitCast x.2))))
      (hnullS.comp (φ := bitCast) (ψ := bitCast) (measurable_of_countable _)
        (measurable_of_countable _))
      hA hB (by rw [hvarA']; norm_num) (by rw [hvarB']; norm_num) hasLaw_sq_chiSquare

end MathlibExtTest.Probability.Statistics.SampleCorrelation
