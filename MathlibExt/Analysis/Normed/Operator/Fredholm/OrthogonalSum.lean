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
# Fredholm maps on orthogonal two-norm sums

Over a nontrivially normed field, let `S : H₀ → H₁` and `T : K₀ → K₁` be bounded Fredholm maps
of normed spaces. Their rectangular block map `(x,y) ↦ (Sx,Ty)` is Fredholm between the
orthogonal two-norm sums.

The conclusion retains strictness, closed finite-codimension range and finite-dimensional
complemented kernel. Neither completeness of the field or spaces nor inner products are assumed.
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

/-- **Fredholm block diagonal on two-norm sums.** Let `𝕜` be a nontrivially normed field and
`H₀,H₁,K₀,K₁` normed `𝕜`-spaces in independent universes. If bounded `S : H₀ → H₁` and `T
: K₀ → K₁` are Fredholm, their block operator `(x,y) ↦ (Sx,Ty)` is Fredholm on the
orthogonal two-norm sums. Fredholmness includes strictness, closed finite-codimension
range and a finite-dimensional complemented kernel. No completeness or inner products are
assumed. -/
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
