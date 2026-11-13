/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianModificationLaw
import Code.SLE.StandardBrownianLaw








open MeasureTheory ProbabilityTheory

namespace StatMech.SLE



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
      (measurable_pi_lambda _ brownianContinuousModification_measurable)]
    simpa only [Function.comp_apply] using
      (standardBrownian_restrict_law
        brownianContinuousModification_isStandardBrownianMotion I).map_eq
  exact hprojective.unique brownianProductLaw_isProjectiveLimit


theorem brownianContinuousModification_sleDriving_processLaw (kappa : Real) :
    brownianProductLaw.map
        (fun omega => sleDriving kappa brownianContinuousModification omega) =
      brownianProductLaw.map
        (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
  let path : (Real -> Real) -> (Real -> Real) :=
    fun omega t => brownianContinuousModification t omega
  let scale : (Real -> Real) -> (Real -> Real) :=
    fun b t => Real.sqrt kappa * b t
  have hpath : Measurable path :=
    measurable_pi_lambda _ brownianContinuousModification_measurable
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

end StatMech.SLE
