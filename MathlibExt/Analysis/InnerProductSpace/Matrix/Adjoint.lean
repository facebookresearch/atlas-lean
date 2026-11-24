/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Topology.Algebra.Module.Matrix
public import MathlibExt.Analysis.InnerProductSpace.Adjoint.OneSided
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rectangular adjoints of operator-valued matrices

The adjoint of the public PiLp column action is the column action of the
transpose of the entry adjoints, with the same finite-product inner
products. The one-sided law requires completeness only of the source
stage. The usual adjoint facade law is a separate both-complete corollary.

No matrix-action copy, new matrix norm or infinite-square-summable carrier
is introduced. Square complete-H specializations supply star compatibility;
CStarMatrix norm/isometry and spatial identifications are separate results.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe uScalar uRow uColumn uSource uTarget

variable {𝕜 : Type uScalar} [RCLike 𝕜]
variable {m : Type uRow} {n : Type uColumn}
variable {E : Type uSource} {F : Type uTarget}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace Matrix

/-- The one-sided adjoint of the rectangular column action is the action of
the transpose of its entry adjoints. The target need not be complete. -/
@[simp]
theorem toPiLpContinuousLinearMap_adjointOfCompleteSource [Fintype m] [Fintype n]
    (M : Matrix m n (E →L[𝕜] F)) :
    ContinuousLinearMap.adjointOfCompleteSource (toPiLpContinuousLinearMap M) =
      toPiLpContinuousLinearMap
        ((M.map fun T : E →L[𝕜] F =>
          ContinuousLinearMap.adjointOfCompleteSource T).transpose) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right 𝕜
  intro v
  simp only [ContinuousLinearMap.adjointOfCompleteSource_inner_left,
    PiLp.inner_apply, toPiLpContinuousLinearMap_apply,
    transpose_apply, map_apply, sum_inner, inner_sum]
  exact Finset.sum_comm

variable [CompleteSpace F]

/-- The usual both-complete adjoint facade is the action of the transpose of
the entry adjoints. No target-completeness weakening of that facade is made. -/
@[simp]
theorem toPiLpContinuousLinearMap_adjoint [Fintype m] [Fintype n]
    (M : Matrix m n (E →L[𝕜] F)) :
    ContinuousLinearMap.adjoint (toPiLpContinuousLinearMap M) =
      toPiLpContinuousLinearMap
        ((M.map fun T : E →L[𝕜] F => ContinuousLinearMap.adjoint T).transpose) := by
  simpa only [ContinuousLinearMap.adjointOfCompleteSource_eq_adjoint] using
    (toPiLpContinuousLinearMap_adjointOfCompleteSource M)

end Matrix

end
