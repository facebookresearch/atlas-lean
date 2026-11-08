/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Truncation
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open ProbabilityTheory.KolmogorovThreeSeries
open scoped NNReal ENNReal Topology

namespace MathlibExtTest.Probability.TruncationCanonicalTests

/-- The closed cutoff keeps its positive boundary. -/
theorem positive_boundary : truncatedRV (fun _ => id) 2 0 (2 : ℝ) = 2 :=
  truncatedRV_eq_of_abs_le (by norm_num)

/-- The closed cutoff keeps its negative boundary. -/
theorem negative_boundary : truncatedRV (fun _ => id) 2 0 (-2 : ℝ) = -2 :=
  truncatedRV_eq_of_abs_le (by norm_num)

/-- A strictly outside value is removed. -/
theorem strict_outside : truncatedRV (fun _ => id) 2 0 (3 : ℝ) = 0 :=
  truncatedRV_eq_zero_of_abs_gt (by norm_num)

/-- The zero cutoff removes nonzero values. -/
theorem zero_cutoff_nonzero : truncatedRV (fun _ => id) 0 0 (1 : ℝ) = 0 :=
  truncatedRV_eq_zero_of_abs_gt (by norm_num)

/-- Every value is removed at a negative cutoff. -/
theorem negative_cutoff (x : ℝ) : truncatedRV (fun _ => id) (-1) 0 x = 0 :=
  truncatedRV_eq_zero_of_abs_gt (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (abs_nonneg x))

/-- The boundary belongs to the cutoff and has zero strict-tail mass. -/
theorem strict_tail_boundary : Measure.dirac (2 : ℝ) {x : ℝ | 2 < |x|} = 0 := by
  simp

/-- A finite measure of mass two needs no probability instance for integrability. -/
theorem finite_nonprobability_integrable :
    Integrable (truncatedRV (fun (_ : ℕ) (_ : ℝ) => (2 : ℝ)) 2 0)
      (Measure.dirac (0 : ℝ) + Measure.dirac (0 : ℝ)) :=
  integrable_truncatedRV 0 measurable_const 2

/-- The public Lp API also covers the top exponent on a finite non-probability measure. -/
theorem finite_nonprobability_top :
    MemLp (truncatedRV (fun (_ : ℕ) (_ : ℝ) => (2 : ℝ)) 2 0) ⊤
      (Measure.dirac (0 : ℝ) + Measure.dirac (0 : ℝ)) :=
  memLp_truncatedRV 0 measurable_const 2 ⊤

/-- The probability assumption in the mean bound is substantive: mass two gives mean four. -/
theorem finite_mass_two_mean :
    (∫ ω, truncatedRV (fun (_ : ℕ) (_ : ℝ) => (2 : ℝ)) 2 0 ω
      ∂(Measure.dirac (0 : ℝ) + Measure.dirac (0 : ℝ))) = 4 := by
  norm_num [truncatedRV_apply, integral_const, measureReal_def, Measure.add_apply]

/-- Bounded canonical truncations need not be integrable on an infinite measure. -/
theorem infinite_measure_not_integrable :
    ¬ Integrable (truncatedRV (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) 1 0)
      (volume : Measure ℝ) := by
  have heq : truncatedRV (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) 1 0 = fun _ => (1 : ℝ) := by
    funext ω
    exact truncatedRV_eq_of_abs_le (by norm_num)
  rw [heq]
  intro hint
  have hfinite := (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp hint
  have hlt := hfinite.measure_univ_lt_top
  simp at hlt

/-- A nonzero geometric family keeps its partial-sum limit even on an infinite measure. -/
theorem geometric_convergence_on_infinite_measure :
    ∃ S : ℝ → ℝ, ∀ᵐ ω ∂(volume : Measure ℝ),
      Tendsto (fun n => (Finset.range n).sum
        (fun i => truncatedRV (fun (k : ℕ) (_ : ℝ) => (1 / 2 : ℝ) ^ k) 1 i ω))
        atTop (nhds (S ω)) := by
  have hsum : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) 2 := by
    have h := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    rwa [show (1 - (1 / 2 : ℝ))⁻¹ = 2 by norm_num] at h
  apply ae_tendsto_truncatedRV_of_bdd
  · intro n ω
    rw [abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · exact ⟨fun _ => 2, Eventually.of_forall fun _ => hsum.tendsto_sum_nat⟩

end MathlibExtTest.Probability.TruncationCanonicalTests
