/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerLDPUpperBound

/-! Non-vacuity tests for the Cramér upper bound: constant sequences. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.CramerUpperBound
open MathlibExt.Probability.CramerRateFunction
open MathlibExt.Probability.CramerLDPUpperBound

namespace MathlibExtTest.Probability.CramerLDPUpperBound

/-- The Cramér rate function of a constant vector is a good rate function. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (c : EuclideanSpace ℝ (Fin d)) :
    IsGoodRateFunction (cramerRateFunction (fun _ : Ω => c) μ) :=
  isGoodRateFunction_cramerRateFunction (μ := μ) (fun _ => c) fun _ => integrable_const _

/-- **Independence of constants.** Constant random vectors on a one-point probability space are
independent. -/
private theorem iIndepFun_const_dirac {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun (_ : ℕ) (_ : Unit) => c) (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, c ∈ sets i
  · have h1 : (⋂ i ∈ S, (fun _ : Unit => c) ⁻¹' sets i) = Set.univ := by
      ext u; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      exact fun i hi => h i hi
    rw [h1, measure_univ]
    refine (Finset.prod_eq_one fun i hi => ?_).symm
    have : (fun _ : Unit => c) ⁻¹' sets i = Set.univ := by
      ext u; simp [h i hi]
    rw [this, measure_univ]
  · push Not at h
    obtain ⟨j, hj, hcj⟩ := h
    have h1 : (⋂ i ∈ S, (fun _ : Unit => c) ⁻¹' sets i) = ∅ := by
      ext u; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false,
        not_forall]
      exact ⟨j, hj, hcj⟩
    rw [h1, measure_empty]
    refine (Finset.prod_eq_zero hj ?_).symm
    have : (fun _ : Unit => c) ⁻¹' sets j = ∅ := by
      ext u; simp [hcj]
    rw [this, measure_empty]

/-- The Cramér upper bound for a constant sequence on a one-point probability space. -/
example {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) {F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsClosed F) :
    Filter.limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
        (empiricalMeanMeasureVec (fun (_ : ℕ) (_ : Unit) => c) (Measure.dirac ()) n F))
        Filter.atTop ≤
      -(⨅ x ∈ F, (cramerRateFunction (fun _ : Unit => c) (Measure.dirac ()) x : EReal)) :=
  limsup_log_empiricalMeanMeasureVec_le (X := fun (_ : ℕ) (_ : Unit) => c)
    (fun _ => measurable_const) (iIndepFun_const_dirac c)
    (fun _ => IdentDistrib.refl aemeasurable_const) (fun _ => integrable_const _) hF

end MathlibExtTest.Probability.CramerLDPUpperBound
