/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

@[expose] public section

open Function Set Filter Topology
open Module End

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointRangeDecomposition

/-!
# Spectral theorem for compact self-adjoint operators: range decomposition

For a compact self-adjoint operator `T` on a Hilbert space `H`, the closed
span of the eigenspaces for *nonzero* eigenvalues is the closure of the
range of `T`, and the closure of the range is complementary to the kernel
of `T`. Together with the orthogonality of the eigenspaces, this is the
range-decomposition form of the spectral theorem for compact self-adjoint
operators.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.spectral_theorem_range_decomposition`
(Theorem (Spectral theorem), May 11, 2021).

The first conclusion is the new content: Mathlib's spectral theorem for
compact self-adjoint operators
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) only
says the orthogonal complement of *all* eigenspaces — including the
eigenspace for `0`, i.e. the kernel — is trivial, and
`MathlibExt.Analysis.InnerProductSpace.CompactSpectral.compactNormal_hilbertBasis`
gives a Hilbert basis of eigenvectors for compact *normal* operators over
`ℂ`. Neither states, for a self-adjoint operator over a general `RCLike`
field, that the closed span of the *nonzero* eigenspaces is the closure of
the range. The proof below follows the v1 proof: if `x` is orthogonal to
every nonzero eigenspace, then `T x` is orthogonal to every eigenspace
(including the kernel, by symmetry), hence `T x = 0` by Mathlib's theorem,
so `x` is in the kernel; the remaining conclusions follow from
`LinearMap.IsSymmetric.orthogonal_range` and double orthogonal complements.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Orthogonal complement of the nonzero-eigenvalue eigenspaces.** Let $H$ be a Hilbert space
over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and let $T : H \to H$ be a compact self-adjoint
bounded linear operator. Then the orthogonal complement of the subspace spanned by the
eigenspaces $\ker(T - \mu I)$ for all nonzero $\mu \in \mathbb{K}$ equals the kernel of $T$. -/
theorem orthogonal_iSup_eigenspaces_ne_zero_eq_ker {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H)) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H))ᗮ =
      LinearMap.ker T.toLinearMap := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have h_span := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hsym
  apply le_antisymm
  · intro x hx
    have hTx_bot : T x ∈ (⨆ μ, eigenspace (T : End 𝕜 H) μ)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      exact Submodule.iSup_induction (p := fun μ => eigenspace (T : End 𝕜 H) μ)
        (motive := fun v => @inner 𝕜 H _ (T x) v = 0) hy
        (fun μ v hv => by
          have hTv := mem_eigenspace_iff.mp hv
          change @inner 𝕜 H _ ((T : H →ₗ[𝕜] H) x) v = 0
          rw [hsym x v, hTv, inner_smul_right]
          by_cases hμ : μ = 0
          · simp [hμ]
          · have hv_mem : v ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0),
                (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H) :=
              Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ hv)
            have := (Submodule.mem_orthogonal' _ _).mp hx v hv_mem
            rw [this, mul_zero])
        (inner_zero_right _)
        (fun a b ha hb => by
          show @inner 𝕜 H _ (T x) (a + b) = 0
          rw [inner_add_right, ha, hb, add_zero])
    rw [h_span, Submodule.mem_bot] at hTx_bot
    exact LinearMap.mem_ker.mpr hTx_bot
  · intro x hx
    rw [Submodule.mem_orthogonal']
    intro y hy
    have hx_eig : x ∈ eigenspace (T : End 𝕜 H) 0 := by
      simp [LinearMap.mem_ker.mp hx]
    exact Submodule.iSup_induction
      (p := fun μ => ⨆ (_ : μ ≠ 0), eigenspace (T : End 𝕜 H) μ)
      (motive := fun v => @inner 𝕜 H _ x v = 0) hy
      (fun μ v hv => by
        by_cases hμ : μ = 0
        · subst hμ; simp at hv; rw [hv, inner_zero_right]
        · have hv' : v ∈ eigenspace (T : End 𝕜 H) μ := by
            simp only [ne_eq, hμ, not_false_eq_true, iSup_true] at hv; exact hv
          exact hsym.orthogonalFamily_eigenspaces (Ne.symm hμ) ⟨x, hx_eig⟩ ⟨v, hv'⟩)
      (inner_zero_right _)
      (fun a b ha hb => by
        show @inner 𝕜 H _ x (a + b) = 0
        rw [inner_add_right, ha, hb, add_zero])

/-- **Spectral theorem for compact self-adjoint operators (range
decomposition form).** Let $H$ be a Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$
and let $T : H \to H$ be a compact self-adjoint bounded linear operator. Then:
(1) the closure of the subspace spanned by the eigenspaces $\ker(T - \mu I)$ for all
nonzero $\mu \in \mathbb{K}$ equals the closure of the range of $T$;
(2) the closure of the range of $T$ and the kernel of $T$ are complementary subspaces: their
intersection is $\{0\}$ and their sum is $H$; and
(3) the eigenspaces $\ker(T - \mu I)$, $\mu \in \mathbb{K}$, are pairwise orthogonal for distinct
values of $\mu$. -/
theorem spectral_theorem_range_decomposition {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H)) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H)).topologicalClosure =
      (LinearMap.range T.toLinearMap).topologicalClosure ∧
    IsCompl (LinearMap.range T.toLinearMap).topologicalClosure (LinearMap.ker T.toLinearMap) ∧
    OrthogonalFamily 𝕜 (fun μ : 𝕜 => eigenspace (T : End 𝕜 H) μ)
      (fun μ => (eigenspace (T : End 𝕜 H) μ).subtypeₗᵢ) := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hort_range : (LinearMap.range T.toLinearMap)ᗮ = LinearMap.ker T.toLinearMap :=
    hsym.orthogonal_range
  have h_ort_nonzero : (⨆ (μ : 𝕜) (_ : μ ≠ 0),
      (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H))ᗮ = LinearMap.ker T.toLinearMap :=
    orthogonal_iSup_eigenspaces_ne_zero_eq_ker hT hc
  refine ⟨?_, ?_, hsym.orthogonalFamily_eigenspaces⟩
  · have h1 : (⨆ (μ : 𝕜) (_ : μ ≠ 0),
        (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H))ᗮ =
        (LinearMap.range T.toLinearMap)ᗮ := by
      rw [h_ort_nonzero, hort_range]
    rw [← Submodule.orthogonal_orthogonal_eq_closure, h1,
        Submodule.orthogonal_orthogonal_eq_closure]
  · have hort_closure : (LinearMap.range T.toLinearMap).topologicalClosure.orthogonal =
        LinearMap.ker T.toLinearMap := by
      rw [Submodule.orthogonal_closure, hort_range]
    have hcomp : CompleteSpace (LinearMap.range T.toLinearMap).topologicalClosure :=
      (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    rw [← hort_closure]
    exact @Submodule.isCompl_orthogonal 𝕜 H _ _ _
      (LinearMap.range T.toLinearMap).topologicalClosure
      (@Submodule.HasOrthogonalProjection.ofCompleteSpace 𝕜 H _ _ _
        (LinearMap.range T.toLinearMap).topologicalClosure hcomp)

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointRangeDecomposition
