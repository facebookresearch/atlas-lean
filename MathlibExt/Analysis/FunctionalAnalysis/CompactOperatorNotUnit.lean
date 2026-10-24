/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Algebra.Algebra.Spectrum.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorNotUnit

/-!
# A compact operator on an infinite-dimensional space is not invertible

A compact operator on an infinite-dimensional normed space cannot be a unit
of the bounded-operator algebra: if it were, composing with its inverse
would make the identity operator compact, and the identity is compact only
on finite-dimensional spaces. In particular such an operator is not
bijective, and `0` lies in its spectrum.

This is not in the pinned Mathlib: Mathlib has the Fredholm alternative for
compact operators (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`, which
requires the eigenvalue/spectral value to be nonzero) and the fact that the
identity is compact iff the space is finite-dimensional
(`isCompactOperator_id_iff_finiteDimensional`), but no statement that a
compact operator on an infinite-dimensional space fails to be invertible.
MathlibExt's Lomonosov file uses the same identity-compact step inside a
private proof (a nonzero compact operator is not a scalar), but does not
state this consequence.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.fredholm_alternative_full` (Theorem (Fredholm alternative))
and `v1/Atlas/IntroductionToFunctionalAnalysis/code/OpenMapping.lean`,
`OpenMapping.bijective_bounded_inverse` (Corollary). The v1 Fredholm
alternative is itself a Mathlib lemma and is not re-ported; the
non-invertibility conclusion drawn here from it (via the identity-compact
argument) is not stated in v1 or in the pinned Mathlib.
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

#print axioms not_isUnit_of_isCompactOperator
#print axioms not_bijective_of_isCompactOperator
#print axioms zero_mem_spectrum_of_isCompactOperator

end MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorNotUnit
