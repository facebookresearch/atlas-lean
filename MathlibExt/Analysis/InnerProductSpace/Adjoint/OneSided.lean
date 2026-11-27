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
# Adjoint operators with only the source complete

For real or complex inner-product spaces `E,F`, with `E` complete and `F` possibly incomplete, a
bounded operator `T : E → F` has the bounded adjoint `T† : F → E` characterized by
`⟨T†y,x⟩=⟨y,Tx⟩`, equivalently `⟨x,T†y⟩=⟨Tx,y⟩`.

If `F` is complete as well, this is the usual bounded Hilbert-space adjoint. Source and target
universes are independent, and zero spaces are allowed.
-/

@[expose] public section

noncomputable section

universe uScalar uSource uTarget

variable {𝕜 : Type uScalar} [RCLike 𝕜]
variable {E : Type uSource} {F : Type uTarget}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

/-- **Bounded adjoint from completeness of the source.** Let `𝕜` be real or complex
(`RCLike`), `E` a complete normed inner-product `𝕜`-space and `F` a normed inner-product
`𝕜`-space, possibly incomplete. for `T : E →L[𝕜] F`, `adjointOfCompleteSource T : F →L[𝕜]
E` is characterized by `⟨T†y,x⟩=⟨y,Tx⟩` for `x ∈ E`, `y ∈ F`. -/
def adjointOfCompleteSource (T : E →L[𝕜] F) : F →L[𝕜] E :=
  (InnerProductSpace.toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.toSesqForm T)

/-- **Left inner-product identity of the one-sided adjoint.** Let `𝕜` be real or complex
(`RCLike`), `E` a complete normed inner-product `𝕜`-space and `F` a normed inner-product
`𝕜`-space, possibly incomplete. for bounded `T : E → F`, `x ∈ E` and `y ∈ F`,
`⟨adjointOfCompleteSource T y,x⟩=⟨y,Tx⟩`. -/
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

/-- **Right inner-product identity of the one-sided adjoint.** Let `𝕜` be real or complex
(`RCLike`), `E` a complete normed inner-product `𝕜`-space and `F` a normed inner-product
`𝕜`-space, possibly incomplete. for bounded `T : E → F`, `x ∈ E` and `y ∈ F`,
`⟨x,adjointOfCompleteSource T y⟩=⟨Tx,y⟩`. -/
theorem adjointOfCompleteSource_inner_right (T : E →L[𝕜] F) (x : E) (y : F) :
    inner 𝕜 x (adjointOfCompleteSource T y) = inner 𝕜 (T x) y := by
  rw [← inner_conj_symm, adjointOfCompleteSource_inner_left, inner_conj_symm]

variable [CompleteSpace F]

/-- **Agreement with the Hilbert adjoint when both spaces are complete.** Let `𝕜` be real or
complex and `E,F` complete normed inner-product `𝕜`-spaces. For every `T : E →L[𝕜] F`,
`adjointOfCompleteSource T=ContinuousLinearMap.adjoint T`. -/
theorem adjointOfCompleteSource_eq_adjoint (T : E →L[𝕜] F) :
    adjointOfCompleteSource T = ContinuousLinearMap.adjoint T := by
  apply (ContinuousLinearMap.eq_adjoint_iff (adjointOfCompleteSource T) T).2
  intro y x
  exact adjointOfCompleteSource_inner_left T x y

end ContinuousLinearMap

end
