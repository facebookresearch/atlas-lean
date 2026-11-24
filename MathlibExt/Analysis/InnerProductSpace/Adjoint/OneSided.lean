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

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoint of an operator with complete source

For a fixed operator `T : E →L[𝕜] F`, completeness of E suffices to
represent `x ↦ inner 𝕜 y (T x)` by a vector in E. The public Riesz inverse
composed with the public sesquilinear-form map gives an actual linear CLM
from F to E: both factors are conjugate-linear.

This construction does not require F to be complete. The comparison with
the usual adjoint facade is stated separately under completeness of F.
-/

@[expose] public section

noncomputable section

universe uScalar uSource uTarget

variable {𝕜 : Type uScalar} [RCLike 𝕜]
variable {E : Type uSource} {F : Type uTarget}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

/-- The adjoint of a fixed operator obtained from the public Riesz inverse.
Only the source E is required to be complete. -/
def adjointOfCompleteSource (T : E →L[𝕜] F) : F →L[𝕜] E :=
  (InnerProductSpace.toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.toSesqForm T)

/-- The one-sided adjoint satisfies the left inner-product characteristic. -/
theorem adjointOfCompleteSource_inner_left (T : E →L[𝕜] F) (x : E) (y : F) :
    inner 𝕜 (adjointOfCompleteSource T y) x = inner 𝕜 y (T x) := by
  change inner 𝕜
    ((InnerProductSpace.toDual 𝕜 E).symm (ContinuousLinearMap.toSesqForm T y)) x =
      inner 𝕜 y (T x)
  rw [InnerProductSpace.toDual_symm_apply]
  calc
    (ContinuousLinearMap.toSesqForm T y) x = ((innerSL 𝕜 y).comp T) x :=
      congrArg (fun f : StrongDual 𝕜 E => f x)
        (ContinuousLinearMap.toSesqForm_apply_coe T y)
    _ = inner 𝕜 y (T x) := rfl

/-- The one-sided adjoint satisfies the right inner-product characteristic. -/
theorem adjointOfCompleteSource_inner_right (T : E →L[𝕜] F) (x : E) (y : F) :
    inner 𝕜 x (adjointOfCompleteSource T y) = inner 𝕜 (T x) y := by
  rw [← inner_conj_symm, adjointOfCompleteSource_inner_left, inner_conj_symm]

variable [CompleteSpace F]

/-- When the target is also complete, the fixed one-sided construction is
the usual adjoint. The facade retains both completeness requirements. -/
theorem adjointOfCompleteSource_eq_adjoint (T : E →L[𝕜] F) :
    adjointOfCompleteSource T = ContinuousLinearMap.adjoint T := by
  apply (ContinuousLinearMap.eq_adjoint_iff (adjointOfCompleteSource T) T).2
  intro y x
  exact adjointOfCompleteSource_inner_left T x y

end ContinuousLinearMap

end
