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

public import MathlibExt.Analysis.InnerProductSpace.OrthogonalSum
public import MathlibExt.Analysis.Normed.Operator.Fredholm.Prod
public import MathlibExt.Analysis.Normed.Operator.Fredholm.Transport

/-!
# Strong Fredholm orthogonal block sums

The existing rectangular block diagonal is transported from the actual
Cartesian product of two strong Fredholm maps through the stock WithLp
continuous linear equivalences. All five strong fields are preserved.
No scalar/stage completeness, Hilbert structure or new norm is required.
-/

@[expose] public section

namespace OrthogonalSum

universe u𝕜 uH₀ uH₁ uK₀ uK₁

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H₀ : Type uH₀} {H₁ : Type uH₁} {K₀ : Type uK₀} {K₁ : Type uK₁}
variable [NormedAddCommGroup H₀] [NormedSpace 𝕜 H₀]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup K₀] [NormedSpace 𝕜 K₀]
variable [NormedAddCommGroup K₁] [NormedSpace 𝕜 K₁]

/-- The actual rectangular orthogonal block of two strong Fredholm maps is
strong Fredholm, without completeness or inner-product hypotheses. -/
theorem isFredholm_blockDiagonal
    (S : H₀ →L[𝕜] H₁) (T : K₀ →L[𝕜] K₁)
    (hS : S.IsFredholm) (hT : T.IsFredholm) :
    (blockDiagonal S T).IsFredholm := by
  let d : OrthogonalSum H₀ K₀ ≃L[𝕜] H₀ × K₀ :=
    WithLp.prodContinuousLinearEquiv 2 𝕜 H₀ K₀
  let c : OrthogonalSum H₁ K₁ ≃L[𝕜] H₁ × K₁ :=
    WithLp.prodContinuousLinearEquiv 2 𝕜 H₁ K₁
  have hOperator : blockDiagonal S T =
      c.symm.toContinuousLinearMap.comp ((S.prodMap T).comp d.toContinuousLinearMap) := by
    ext x
    rfl
  rw [hOperator]
  exact (hS.prodMap hT).transport d c

end OrthogonalSum
