/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedMultiplierStrict
import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedCoefficientActions
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# Completed crossed-product action consumers at a zero seminorm

The coefficient algebra is genuinely nonunital. Its group action is the
computed trivial action, and the C-star seminorm is zero. Admissibility is
proved by the existing L1-gauge theorem, rather than assumed as a model bound.
Group universes and Haar/regular-measure hypotheses remain independent.
-/

noncomputable section
open MeasureTheory HaarTwistedCore
open scoped ZeroAtInfty MultiplierAlgebra
namespace CompletedCrossedActionsSmoke
universe uG

private abbrev Coefficients := C₀(ℝ, ℂ)
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

private abbrev action := PointNormCStarAction.trivial G Coefficients
private abbrev zeroSeminorm := (0 : CStarSeminorm (Carrier μ (action (G := G))))
attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

example (x : (zeroSeminorm μ).NonUnitalCompletion) :
    groupLeftCompletion μ (action (G := G)) (zeroSeminorm μ) 1 x = x := by
  simp only [groupLeftCompletion_one, ContinuousLinearMap.id_apply]

example (x : (zeroSeminorm μ).NonUnitalCompletion) :
    groupRightCompletion μ (action (G := G)) (zeroSeminorm μ) 1 x = x := by
  simp only [groupRightCompletion_one, ContinuousLinearMap.id_apply]

example (x : (zeroSeminorm μ).NonUnitalCompletion) :
    coefficientLeftCompletion μ (action (G := G)) (zeroSeminorm μ) (0 : Coefficients) x = 0 := by
  simp only [coefficientLeftCompletion_zero, zero_apply]

example (x : (zeroSeminorm μ).NonUnitalCompletion) :
    coefficientRightCompletion μ (action (G := G)) (zeroSeminorm μ) (0 : Coefficients) x = 0 := by
  simp only [coefficientRightCompletion_zero, zero_apply]

example (g : G) (x : (zeroSeminorm μ).NonUnitalCompletion) :
    ‖groupLeftCompletion μ (action (G := G)) (zeroSeminorm μ) g x‖ = ‖x‖ :=
  norm_groupLeftCompletion_apply μ (action (G := G)) (zeroSeminorm μ) g x

-- The public star exchange is tested after the actual function-star compiler port.
example (g : G) (x : (zeroSeminorm μ).NonUnitalCompletion) :
    star (groupLeftCompletion μ (action (G := G)) (zeroSeminorm μ) g x) =
      groupRightCompletion μ (action (G := G)) (zeroSeminorm μ) g⁻¹ (star x) :=
  star_groupLeftCompletion μ (action (G := G)) (zeroSeminorm μ) g x

-- Trivial action gives commuting computed coefficient and group multipliers.
example (g : G) (a : Coefficients) :
    groupMultiplier μ (action (G := G)) (zeroSeminorm μ) g *
        coefficientMultiplier μ (action (G := G)) (zeroSeminorm μ) a =
      coefficientMultiplier μ (action (G := G)) (zeroSeminorm μ) a *
        groupMultiplier μ (action (G := G)) (zeroSeminorm μ) g := by
  simpa only [action, PointNormCStarAction.trivial_apply] using
    groupMultiplier_coefficientMultiplier μ (action (G := G)) (zeroSeminorm μ) g a

-- The actual strict pair factory accepts its internally earned zero-seminorm bound.
example : DoubleCentralizer.StrictContinuous (fun g : G =>
    ((canonicalStrictMultiplierPair μ (action (G := G)) (zeroSeminorm μ)
      (zero_mem_admissibleCStarSeminorms μ (action (G := G)))).val.2 g :
        𝓜(ℂ, (zeroSeminorm μ).NonUnitalCompletion))) :=
  canonicalStrictMultiplierPair_strictContinuous μ (action (G := G)) (zeroSeminorm μ)
    (zero_mem_admissibleCStarSeminorms μ (action (G := G)))

end CompletedCrossedActionsSmoke
