/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.BrownianMotion.BrownianModificationLaw
public import MathlibExt.Probability.BrownianMotion.StandardBrownianLaw

/-!
# The path law of the canonical Brownian motion

The continuous modification `B̃` of the coordinate process on `(ℝ → ℝ, brownianProductLaw)` has
path law `brownianProductLaw` itself, and the law of its SLE driving function `√κ B̃` is the
image of `brownianProductLaw` under scaling by `√κ`. Restricted to `t ≥ 0`, `B̃` is a Brownian
motion in Mathlib's sense (`brownianContinuousModification_isBrownianReal`), which Mathlib defines
but does not construct.

## Main results

* `StatMech.SLE.brownianContinuousModification_processLaw`.
* `StatMech.SLE.brownianContinuousModification_isBrownianReal`: existence of a process satisfying
  Mathlib's `IsBrownianReal`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StatMech.SLE

/-- The path law of the continuous modification on `ℝ → ℝ` is `brownianProductLaw`. -/
theorem brownianContinuousModification_processLaw :
    brownianProductLaw.map
      (fun omega t => brownianContinuousModification t omega) =
        brownianProductLaw := by
  have hprojective : IsProjectiveLimit
      (brownianProductLaw.map
        (fun omega t => brownianContinuousModification t omega))
      brownianFiniteDimensionalPiLaw := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I)
      (Measurable.of_eval brownianContinuousModification_measurable)]
    exact
      (standardBrownian_restrict_law
        brownianContinuousModification_isStandardBrownianMotion I).map_eq
  exact hprojective.unique brownianProductLaw_isProjectiveLimit

/-- The path law of `√κ B̃` is the image of `brownianProductLaw` under scaling by `√κ`. -/
theorem brownianContinuousModification_sleDriving_processLaw (kappa : Real) :
    brownianProductLaw.map
        (fun omega => sleDriving kappa brownianContinuousModification omega) =
      brownianProductLaw.map
        (fun b : Real → Real => fun t => Real.sqrt kappa * b t) := by
  let path : (Real → Real) → (Real → Real) :=
    fun omega t => brownianContinuousModification t omega
  let scale : (Real → Real) → (Real → Real) :=
    fun b t => Real.sqrt kappa * b t
  have hpath : Measurable path :=
    Measurable.of_eval brownianContinuousModification_measurable
  have hscale : Measurable scale := measurable_sleDrivingPath kappa
  calc
    brownianProductLaw.map
        (fun omega => sleDriving kappa brownianContinuousModification omega) =
      brownianProductLaw.map (scale ∘ path) := by rfl
    _ = (brownianProductLaw.map path).map scale := by
      rw [Measure.map_map hscale hpath]
    _ = brownianProductLaw.map scale := by
      rw [show brownianProductLaw.map path = brownianProductLaw by
        exact brownianContinuousModification_processLaw]

/-- The canonical Brownian motion restricted to times `t ≥ 0` satisfies Mathlib's
`ProbabilityTheory.IsBrownianReal`. Mathlib defines Brownian motion but does not construct one;
this is an unconditional existence statement for it. -/
theorem brownianContinuousModification_isBrownianReal :
    IsBrownianReal (fun (t : ℝ≥0) ω => brownianContinuousModification t ω) brownianProductLaw :=
  brownianContinuousModification_isStandardBrownianMotion.isBrownianReal

end StatMech.SLE
