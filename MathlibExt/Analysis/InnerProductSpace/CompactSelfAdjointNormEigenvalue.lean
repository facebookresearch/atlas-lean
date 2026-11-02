/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

open ContinuousLinearMap
open scoped ComplexConjugate

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalue

/-!
# An eigenvalue of maximal modulus for a compact self-adjoint operator

For a nonzero compact self-adjoint operator `T` on a Hilbert space, an
eigenvalue of modulus `‖T‖` is attained: there is a unit vector `u` with
`T u = r • u` for a real scalar `r` with `|r| = ‖T‖`. This is the first
step of the maximum principle for compact self-adjoint operators — the
book's Theorem (Maximum principle), May 11, 2021 section, orders all the
nonzero eigenvalues by decreasing modulus and shows they tend to `0`; the
full ordered sequence is not proved here, only its first (largest) term.

The proof is short: for a self-adjoint `T`, Mathlib's
`ContinuousLinearMap.spectralRadius_eq_nnnorm` says the spectral radius
equals `‖T‖`, so the spectrum is nonempty when `T ≠ 0`; the spectral
radius is attained at some `μ ∈ spectrum 𝕜 T` by
`spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty`; and a nonzero
point of the spectrum of a compact operator is an eigenvalue by the
Fredholm alternative (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`).
The eigenvalue is real because `T` is self-adjoint, and the eigenvector is
normalized to a unit vector.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.compact_selfAdjoint_maximum_principle`
(Theorem (Maximum principle), May 11, 2021). The v1 formalization of that
theorem is left unproved; it is not ported. The statement below is the
first-step consequence proved here from scratch.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The spectrum of a nonzero self-adjoint operator is nonempty: if it
were empty, the spectral radius would be `0`, contradicting
`spectralRadius_eq_nnnorm`. -/
private theorem spectrum_nonempty_of_ne_zero (T : H →L[𝕜] H) (hT : IsSelfAdjoint T)
    (hT0 : T ≠ 0) : (spectrum 𝕜 T).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have h0 : spectralRadius 𝕜 T = 0 := by
    rw [spectralRadius_eq_of_unital, h]
    simp
  rw [T.spectralRadius_eq_nnnorm hT] at h0
  exact hT0 (by simpa using h0)

/-- **A nonzero compact self-adjoint operator has an eigenvalue of modulus equal to its norm.**
Let $T \neq 0$ be a compact self-adjoint operator on a Hilbert space $H$ over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $T$ has an eigenvalue $\mu \in \mathbb{K}$ with
$\mu \neq 0$ and $|\mu| = \|T\|$, where $\|T\|$ is the operator norm of $T$. -/
theorem exists_hasEigenvalue_norm_eq (T : H →L[𝕜] H) (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hT0 : T ≠ 0) :
    ∃ μ : 𝕜, μ ≠ 0 ∧ ‖μ‖ = ‖T‖ ∧ Module.End.HasEigenvalue (T : Module.End 𝕜 H) μ := by
  obtain ⟨μ, hμspec, hμμ⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
      (spectrum_nonempty_of_ne_zero T hT hT0)
  rw [T.spectralRadius_eq_nnnorm hT] at hμμ
  have h2 : ‖μ‖₊ = ‖T‖₊ := by exact_mod_cast hμμ
  have hnorm : ‖μ‖ = ‖T‖ := by
    calc ‖μ‖ = (‖μ‖₊ : ℝ) := coe_nnnorm μ
      _ = (‖T‖₊ : ℝ) := by rw [h2]
      _ = ‖T‖ := (coe_nnnorm T).symm
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hT0 (norm_eq_zero.mp hnorm.symm)
  exact ⟨μ, hμ0, hnorm, (hc.hasEigenvalue_iff_mem_spectrum hμ0).mpr hμspec⟩

/-- **A nonzero compact self-adjoint operator has a real eigenvalue of modulus equal to its norm,
with a unit eigenvector.** Let $T \neq 0$ be a compact self-adjoint operator on a Hilbert space
$H$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then there are a real number $r$ and a unit
vector $u \in H$ with $T u = r u$ and $|r| = \|T\|$, where $\|T\|$ is the operator norm of $T$. -/
theorem exists_unit_eigenvector_real_eigenvalue (T : H →L[𝕜] H) (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hT0 : T ≠ 0) :
    ∃ r : ℝ, ∃ u : H, ‖u‖ = 1 ∧ T u = (r : 𝕜) • u ∧ |r| = ‖T‖ := by
  obtain ⟨μ, _hμ0, hnorm, heig⟩ := exists_hasEigenvalue_norm_eq T hT hc hT0
  -- The eigenvalue is real, since `T` is self-adjoint.
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hconj : conj μ = μ := hsym.conj_eigenvalue_eq_self heig
  have hμreal : (RCLike.re μ : 𝕜) = μ := RCLike.conj_eq_iff_re.mp hconj
  obtain ⟨u₀, hu₀mem, hu₀ne⟩ := heig.exists_hasEigenvector
  have hu₀T : T u₀ = μ • u₀ := Module.End.mem_eigenspace_iff.mp hu₀mem
  have hu₀norm : ‖u₀‖ ≠ 0 := norm_ne_zero_iff.mpr hu₀ne
  -- Normalize `u₀` to a unit vector.
  set c : 𝕜 := ((‖u₀‖⁻¹ : ℝ) : 𝕜) with hc_def
  refine ⟨RCLike.re μ, c • u₀, ?_, ?_, ?_⟩
  · rw [norm_smul]
    have hcnorm : ‖c‖ = ‖u₀‖⁻¹ := by
      rw [hc_def, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    rw [hcnorm, inv_mul_cancel₀ hu₀norm]
  · calc T (c • u₀) = c • T u₀ := map_smul T c u₀
      _ = c • (μ • u₀) := by rw [hu₀T]
      _ = μ • (c • u₀) := smul_comm c μ u₀
      _ = (RCLike.re μ : 𝕜) • (c • u₀) := by rw [hμreal]
  · have hμabs : ‖μ‖ = |RCLike.re μ| := by
      conv_lhs => rw [← hμreal]
      exact RCLike.norm_ofReal _
    rw [← hμabs, hnorm]

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalue
