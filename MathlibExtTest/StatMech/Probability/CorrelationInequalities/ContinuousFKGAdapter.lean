/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ContinuousFKGAdapter
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ContinuousFKGAdapter`

* `fkg_of_subset_coords` on `[0, 1]³` for functions of the coordinate subset `{0}`.
* `cube 2` is a probability measure and unfolds to the product of uniform measures.
-/

@[expose] public section

open MeasureTheory
open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ContinuousFKGAdapter

example : IsProbabilityMeasure (cube 2) := inferInstance

example : cube 2 = Measure.pi (fun _ : Fin 2 => volume.restrict (Set.Icc (0 : ℝ) 1)) := cube_eq 2

/-- `y ↦ arctan (y ⟨0, _⟩)` on functions of the coordinate subset `{0}` of `Fin 3`. -/
noncomputable def g : ({i // i ∈ ({0} : Finset (Fin 3))} → ℝ) → ℝ :=
  fun y => Real.arctan (y ⟨0, Finset.mem_singleton_self 0⟩)

theorem g_bound (y : {i // i ∈ ({0} : Finset (Fin 3))} → ℝ) : |g y| ≤ Real.pi / 2 :=
  abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

example : (∫ x, g (restrictCoords {0} x) ∂(cube 3)) * (∫ x, g (restrictCoords {0} x) ∂(cube 3))
    ≤ ∫ x, g (restrictCoords {0} x) * g (restrictCoords {0} x) ∂(cube 3) :=
  fkg_of_subset_coords {0} (Real.continuous_arctan.measurable.comp (measurable_pi_apply _))
    (Real.continuous_arctan.measurable.comp (measurable_pi_apply _)) g_bound g_bound
    (fun _ _ h => Real.arctan_strictMono.monotone (h _))
    (fun _ _ h => Real.arctan_strictMono.monotone (h _))

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ContinuousFKGAdapter
