/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerLDPLowerBound

/-! Non-vacuity tests for Cramér's theorem in `ℝᵈ`: constant sequences. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.CramerUpperBound
open MathlibExt.Probability.CramerRateFunction
open MathlibExt.Probability.CramerLDPLowerBound

namespace MathlibExtTest.Probability.CramerLDPLowerBound

/-- **Independence of constants.** Constant random vectors on a one-point probability space are
independent. -/
private theorem iIndepFun_const_dirac' {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) :
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

/-- Cramér's theorem for a constant sequence on a one-point probability space. -/
example {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) :
    SatisfiesLDP (empiricalMeanMeasureVec (fun (_ : ℕ) (_ : Unit) => c) (Measure.dirac ()))
        (cramerRateFunction (fun _ : Unit => c) (Measure.dirac ())) ∧
      IsGoodRateFunction (cramerRateFunction (fun _ : Unit => c) (Measure.dirac ())) :=
  satisfiesLDP_empiricalMeanMeasureVec (X := fun (_ : ℕ) (_ : Unit) => c)
    (fun _ => measurable_const) (iIndepFun_const_dirac' c)
    (fun _ => IdentDistrib.refl aemeasurable_const) (fun _ => integrable_const _)

/-- The log moment generating function of a constant vector is differentiable. -/
example {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ (logMGFVec (fun _ : Unit => c) (Measure.dirac ())) :=
  differentiable_logMGFVec _ measurable_const fun _ => integrable_const _

end MathlibExtTest.Probability.CramerLDPLowerBound
