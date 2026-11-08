/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauder
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Hilbert-space adjoint-range corollaries

Source context: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.fredholm_alternative_full` (May 11, 2021), the archived
self-adjoint Hilbert-space Fredholm alternative. The range corollaries here
apply to general compact `T` at nonzero `μ`. They use the Banach-space
closed-range result and Mathlib's range/adjoint orthogonality; the adjoint
identity follows from Mathlib's star rules. The archived proof is not imported.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.RieszSchauder

open MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauder
open scoped InnerProduct

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {T : E →L[𝕜] E} {μ : 𝕜}

/-- **Riesz–Schauder theorem on a Hilbert space.** For a compact operator `T` and
`μ ≠ 0`, the range of `μ • 1 - T` is the orthogonal complement of the kernel
of its adjoint. This follows from closedness of the range (the Banach-space
Riesz–Schauder theorem) and Mathlib's `ContinuousLinearMap.orthogonal_range`.
For self-adjoint `T` this recovers `Range (μ • 1 - T) = (ker (μ • 1 - T))ᗮ`. -/
theorem range_eq_orthogonal_ker_adjoint (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    LinearMap.range ((μ • 1 - T : E →L[𝕜] E).toLinearMap)
      = (LinearMap.ker ((μ • 1 - T : E →L[𝕜] E)†.toLinearMap))ᗮ := by
  have hclosed := isClosed_range_smul_one_sub hT hμ
  calc LinearMap.range ((μ • 1 - T : E →L[𝕜] E).toLinearMap)
      = (LinearMap.range ((μ • 1 - T : E →L[𝕜] E).toLinearMap))ᗮᗮ := by
        rw [Submodule.orthogonal_orthogonal_eq_closure,
          hclosed.submodule_topologicalClosure_eq]
    _ = (LinearMap.ker ((μ • 1 - T : E →L[𝕜] E)†.toLinearMap))ᗮ := by
        rw [(μ • 1 - T : E →L[𝕜] E).orthogonal_range]

/-- The adjoint of `μ • 1 - T` is `star μ • 1 - T†`. -/
theorem adjoint_smul_one_sub :
    (μ • 1 - T : E →L[𝕜] E)† = star μ • 1 - T† := by
  simp [← ContinuousLinearMap.star_eq_adjoint]

/-- **Riesz–Schauder theorem on a Hilbert space, adjoint form.** The range of
`μ • 1 - T` is the orthogonal complement of the kernel of `star μ • 1 - T†`. -/
theorem range_eq_orthogonal_ker_smul_one_sub_adjoint (hT : IsCompactOperator T)
    (hμ : μ ≠ 0) :
    LinearMap.range ((μ • 1 - T : E →L[𝕜] E).toLinearMap)
      = (LinearMap.ker ((star μ • 1 - T† : E →L[𝕜] E).toLinearMap))ᗮ := by
  rw [← adjoint_smul_one_sub]
  exact range_eq_orthogonal_ker_adjoint hT hμ

end

end MathlibExt.Analysis.InnerProductSpace.RieszSchauder
