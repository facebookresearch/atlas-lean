/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TalagrandConcentrationTalagrandConcentrationMean
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic.NormNum

/-!
# Tests for Talagrand's concentration inequality around the mean

The Euclidean norm of a uniform random vector in the unit cube has a Gaussian tail
around its expectation, with constants independent of the dimension.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Theorem 2.1.13, inequality `(2.19)`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.TalagrandConcentrationTalagrandConcentrationMean

open MeasureTheory ProbabilityTheory Real
open scoped unitInterval

/-- The Euclidean norm of the uniform unit cube satisfies a dimension-free tail bound. -/
theorem uniform_cube_norm_tail :
    ∃ C > 0, ∃ c > 0, ∀ (n : ℕ) (t : ℝ), 0 < t →
      (Measure.pi (fun _ : Fin n => (volume : Measure I))).real
        {x | t ≤ |‖WithLp.toLp 2 (fun i => (x i : ℝ))‖ -
          ∫ y, ‖WithLp.toLp 2 (fun i => (y i : ℝ))‖
            ∂Measure.pi (fun _ : Fin n => (volume : Measure I))|} ≤ C * exp (-c * t ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ :=
    MathlibExt.Probability.TalagrandConcentrationWanted.talagrand_concentration_mean
  refine ⟨C, hC, c, hc, fun n t ht => ?_⟩
  have hXm : ∀ i : Fin n, Measurable (fun x : Fin n → I => (x i : ℝ)) :=
    fun i => measurable_subtype_coe.comp (measurable_pi_apply i)
  have hXi : iIndepFun (fun (i : Fin n) (x : Fin n → I) => (x i : ℝ))
      (Measure.pi fun _ => (volume : Measure I)) :=
    iIndepFun_pi (fun _ => measurable_subtype_coe.aemeasurable)
  have hX : ∀ (i : Fin n) (x : Fin n → I), |(x i : ℝ)| ≤ 1 := by
    intro i x
    rw [abs_of_nonneg (x i).property.1]
    exact (x i).property.2
  simpa only [mul_one] using h (Fin n → I) inferInstance
    (Measure.pi fun _ => (volume : Measure I)) inferInstance n
    (fun i x => (x i : ℝ)) 1 (by norm_num) hXm hXi hX norm
    convexOn_univ_norm lipschitzWith_one_norm t ht

end MathlibExtTest.Probability.TalagrandConcentrationTalagrandConcentrationMean
