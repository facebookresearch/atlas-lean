/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorNotUnit

@[expose] public section

open MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorNotUnit

namespace MathlibExtTest.Analysis.FunctionalAnalysis.CompactOperatorNotUnit

/-!
# Tests for non-invertibility of compact operators

The abstract examples check the theorems on a hypothetical compact operator.
The finite-dimensional example shows the infinite-dimensional hypothesis is
sharp: on `Fin 2 → ℝ` the identity operator is both a unit and compact.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A compact operator on an infinite-dimensional space is not a unit. -/
example (hInf : ¬ FiniteDimensional 𝕜 E) (T : E →L[𝕜] E)
    (hT : IsCompactOperator (T : E → E)) : ¬ IsUnit T :=
  not_isUnit_of_isCompactOperator hInf T hT

/-- A compact operator on an infinite-dimensional Banach space is not
bijective. -/
example [CompleteSpace E] (hInf : ¬ FiniteDimensional 𝕜 E) (T : E →L[𝕜] E)
    (hT : IsCompactOperator (T : E → E)) : ¬ Function.Bijective T :=
  not_bijective_of_isCompactOperator hInf T hT

/-- Zero lies in the spectrum of a compact operator on an
infinite-dimensional space. -/
example (hInf : ¬ FiniteDimensional 𝕜 E) (T : E →L[𝕜] E)
    (hT : IsCompactOperator (T : E → E)) : (0 : 𝕜) ∈ spectrum 𝕜 T :=
  zero_mem_spectrum_of_isCompactOperator hInf T hT

/-- Sharpness: on the finite-dimensional space `Fin 2 → ℝ`, the identity
operator is both a unit and compact, so the infinite-dimensional hypothesis
cannot be dropped. -/
example : IsUnit (1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) ∧
    IsCompactOperator ((1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :
      (Fin 2 → ℝ) → (Fin 2 → ℝ)) := by
  refine ⟨isUnit_one, ?_⟩
  have hcoe : ((1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :
      (Fin 2 → ℝ) → (Fin 2 → ℝ)) = id := by
    funext x
    rfl
  rw [hcoe]
  exact isCompactOperator_id

end MathlibExtTest.Analysis.FunctionalAnalysis.CompactOperatorNotUnit
