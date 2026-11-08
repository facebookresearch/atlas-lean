/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Algebra.Algebra.Spectrum.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorNotUnit

/-!
# A compact operator on an infinite-dimensional space is not invertible

A compact operator on an infinite-dimensional normed space cannot be a unit
of the bounded-operator algebra: if it were, composing with its inverse
would make the identity operator compact, and the identity is compact only
on finite-dimensional spaces. Consequently `0` lies in its spectrum.
On a Banach space, such an operator is also not bijective.

The non-unit proof composes a compact operator with a bounded inverse
using `IsCompactOperator.clm_comp`, then contradicts infinite dimension
using `FiniteDimensional.of_isCompactOperator_id`. The Banach-space
corollary uses `ContinuousLinearMap.isUnit_iff_bijective`; the spectral
conclusion uses `spectrum.zero_mem_iff`.

Bounded-inverse provenance for the Banach-space corollary is
`v1/Atlas/IntroductionToFunctionalAnalysis/code/OpenMapping.lean`,
`OpenMapping.bijective_bounded_inverse` (Corollary).
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **A compact operator on an infinite-dimensional space is not a unit.**
If `T` is compact and `E` is infinite-dimensional, then `T` has no
two-sided inverse among bounded operators. (Completeness of `E` is not
needed for this statement.) -/
theorem not_isUnit_of_isCompactOperator (hInf : ¬ FiniteDimensional 𝕜 E)
    (T : E →L[𝕜] E) (hT : IsCompactOperator (T : E → E)) : ¬ IsUnit T := by
  rintro hU
  obtain ⟨B, -, hBT⟩ := isUnit_iff_exists.mp hU
  have hcomp : IsCompactOperator (B ∘ (T : E → E)) := hT.clm_comp B
  have hid : (B : E → E) ∘ (T : E → E) = id := by
    funext x
    have h : (B * T) x = (1 : E →L[𝕜] E) x := by rw [hBT]
    rw [mul_apply_eq_comp] at h
    exact h
  rw [hid] at hcomp
  exact hInf (FiniteDimensional.of_isCompactOperator_id hcomp)

/-- **A compact operator on an infinite-dimensional Banach space is not
bijective.** This is the bounded-inverse form of the previous statement. -/
theorem not_bijective_of_isCompactOperator [CompleteSpace E]
    (hInf : ¬ FiniteDimensional 𝕜 E) (T : E →L[𝕜] E)
    (hT : IsCompactOperator (T : E → E)) : ¬ Function.Bijective T := by
  intro hBij
  exact not_isUnit_of_isCompactOperator hInf T hT
    (ContinuousLinearMap.isUnit_iff_bijective.mpr hBij)

/-- **Zero lies in the spectrum of a compact operator on an
infinite-dimensional space.** -/
theorem zero_mem_spectrum_of_isCompactOperator (hInf : ¬ FiniteDimensional 𝕜 E)
    (T : E →L[𝕜] E) (hT : IsCompactOperator (T : E → E)) :
    (0 : 𝕜) ∈ spectrum 𝕜 T :=
  (spectrum.zero_mem_iff 𝕜).mpr (not_isUnit_of_isCompactOperator hInf T hT)

end MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorNotUnit
