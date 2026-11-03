/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.Defs

/-!
# Continuity of SLE driving functions

For a continuous sample path `t ↦ B_t(ω)`, the driving function `√κ B_t(ω)` is continuous.
This is a pathwise fact: it does not use a Brownian-motion law or assert existence of a global
Loewner flow.

The maximal-domain evolution is developed in `LoewnerMaximal`. In `LoewnerCapacity`,
`coeff_ode_solution` solves the coefficient equation from a zero initial value and derivative `2`;
`loewner_halfplane_capacity_eq` additionally assumes a capacity expansion.
Deriving the expansion and its rate from the Loewner equation is not proved here.

## Main results

* `continuous_sleDriving`: continuity of the driving function from continuity of the sample path.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, Mathematical Surveys and Monographs
  114, Amer. Math. Soc., 2005, Chapters 4 and 6.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace StatMech.SLE

/-- The SLE driving function `√κ B_t(ω)` is continuous when `t ↦ B_t(ω)` is. -/
lemma continuous_sleDriving {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω)
    (hcont : Continuous fun t => B t ω) : Continuous (sleDriving κ B ω) := by
  unfold sleDriving
  exact continuous_const.mul hcont

end StatMech.SLE
