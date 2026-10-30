/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.RingTheory.Finiteness.Basic
import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalue
import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvalues

@[expose] public section

open ContinuousLinearMap InnerProductSpace
open Filter Topology
open scoped ComplexConjugate

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteRankApprox

/-!
# Finite-rank approximation of compact self-adjoint operators

A compact self-adjoint operator `T` on a Hilbert space is a norm limit of
finite-rank self-adjoint operators: for every `ε > 0` there is a self-adjoint
`F` of finite rank with `‖T - F‖ ≤ ε`. This is a direct consequence of the
book's spectral theorem / maximum principle for compact self-adjoint
operators (Theorem (Maximum principle), May 11, 2021 section, and Theorem
(Spectral theorem), May 11, 2021 section): keep only the eigenspaces for
eigenvalues of modulus at least `ε` — there are only finitely many such
eigenvalues, and each eigenspace is finite-dimensional — and take `F` to be
the compression of `T` to their span. The difference `T - F` is the
compression of `T` to the orthogonal complement, which has no eigenvalue of
modulus `> ε`, so its norm is at most `ε` (otherwise the norm-attained
eigenvalue of the compression would be an eigenvalue of `T` of modulus
`> ε`, contradicting the choice of the span).

The v1 formalization of the maximum principle is left unproved and is not
ported here. The finite-rank compression argument below uses existing
eigenvalue results. The finiteness argument was closely adapted from
`CompactSpectralWanted.aux_finite_eigenvalues` in
`MathlibExt/Analysis/InnerProductSpace/CompactSpectral.lean`, replacing
normality over `ℂ` by self-adjointness over `RCLike`; this module now uses
the canonical public
`CompactSelfAdjointFiniteEigenvalues.finite_eigenvalues_of_ge`.
The norm-attained eigenvalue is supplied by
`CompactSelfAdjointNormEigenvalue.exists_hasEigenvalue_norm_eq`.
The finite-rank compression and its norm estimate are proved here.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.compact_selfAdjoint_maximum_principle` and
`SpectralTheory.spectral_theorem_range_decomposition`
(Theorem (Maximum principle) and Theorem (Spectral theorem), May 11, 2021).
The full ordered eigenvalue sequence of the maximum principle is not proved
here, only the finite-rank approximation above.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **A nonzero compact self-adjoint operator has an eigenvalue of norm
`‖T‖`.** -/
private theorem exists_hasEigenvalue_norm_eq (T : H →L[𝕜] H) (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hT0 : T ≠ 0) :
    ∃ μ : 𝕜, μ ≠ 0 ∧ ‖μ‖ = ‖T‖ ∧ Module.End.HasEigenvalue (T : Module.End 𝕜 H) μ := by
  exact CompactSelfAdjointNormEigenvalue.exists_hasEigenvalue_norm_eq T hT hc hT0

/-- **Finiteness of eigenvalues bounded away from zero.** For a compact
self-adjoint operator `T` and any `ε > 0`, the set of eigenvalues `μ` of `T`
with `ε ≤ ‖μ‖` is finite. -/
private theorem finite_eigenvalues_of_ge {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : 𝕜 | Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧ ε ≤ ‖μ‖} := by
  exact CompactSelfAdjointFiniteEigenvalues.finite_eigenvalues_of_ge hT hc hε

omit [CompleteSpace H] in
/-- The span of a finite family of eigenspaces is invariant under `T`:
every eigenspace is invariant, and the span of invariant subspaces is
invariant. -/
private theorem map_eigenspace_iSup_le {T : H →L[𝕜] H} {s : Finset 𝕜} :
    Submodule.map (T : H →ₗ[𝕜] H)
        (⨆ μ ∈ s, Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) ≤
      ⨆ μ ∈ s, Module.End.eigenspace (T : H →ₗ[𝕜] H) μ := by
  rw [Submodule.map_iSup]
  apply iSup_le
  intro μ
  rw [Submodule.map_iSup]
  apply iSup_le
  intro hμ
  apply le_trans _ (le_iSup _ μ)
  apply le_trans _ (le_iSup _ hμ)
  rintro y ⟨x, hx, rfl⟩
  have hxT : (T : H →ₗ[𝕜] H) x = μ • x := Module.End.mem_eigenspace_iff.mp hx
  rw [hxT]
  exact Submodule.smul_mem _ _ hx

/-- If a subspace `E` is invariant under a self-adjoint operator `T`, then
its orthogonal complement is invariant too. -/
private theorem orthogonalComplement_invariant {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    {E : Submodule 𝕜 H} (hE : ∀ x ∈ E, T x ∈ E) :
    ∀ v ∈ Eᗮ, T v ∈ Eᗮ := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  intro v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  have hTu : T u ∈ E := hE u hu
  have h0 : @inner 𝕜 H _ (T u) v = 0 := hv (T u) hTu
  have h0' : @inner 𝕜 H _ ((T : H →ₗ[𝕜] H) u) v = 0 := h0
  rw [hsym u v] at h0'
  exact h0'

/-- The norm of the compression of `T` to the orthogonal complement of a
subspace `E` is at most `ε`, provided every eigenvalue of `T` of modulus at
least `ε` has its eigenspace contained in `E`. Otherwise the
norm-attained eigenvalue of the compression would be such an eigenvalue,
with an eigenvector in `Eᗮ ∩ E = ⊥`. -/
private theorem norm_compression_le {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) {ε : ℝ} (hε : 0 < ε)
    {E : Submodule 𝕜 H} [E.HasOrthogonalProjection]
    (hEgen : ∀ μ : 𝕜, Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ → ε ≤ ‖μ‖ →
      Module.End.eigenspace (T : H →ₗ[𝕜] H) μ ≤ E)
    (hEinv : ∀ x ∈ E, T x ∈ E) :
    ‖Eᗮ.starProjection ∘L T ∘L Eᗮ.starProjection‖ ≤ ε := by
  classical
  set Q : H →L[𝕜] H := Eᗮ.starProjection with hQdef
  set C : H →L[𝕜] H := Q ∘L T ∘L Q with hCdef
  have hCsa : IsSelfAdjoint C := hT.conj_starProjection Eᗮ
  have hCcomp : IsCompactOperator (C : H → H) := by
    have h1 : IsCompactOperator ((T : H → H) ∘ (Q : H → H)) := hc.comp_clm Q
    have h2 : IsCompactOperator ((Q : H → H) ∘ ((T : H → H) ∘ (Q : H → H))) :=
      h1.continuous_comp Q.continuous
    simpa [C, ContinuousLinearMap.coe_comp, Function.comp_assoc] using h2
  by_contra hgt
  push Not at hgt
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hgt
    exact absurd hgt (not_lt_of_ge (le_of_lt hε))
  obtain ⟨μ, hμ0, hμnorm, heig⟩ := exists_hasEigenvalue_norm_eq C hCsa hCcomp hC0
  obtain ⟨v, hv_mem, hv_ne⟩ := heig.exists_hasEigenvector
  have hvC : C v = μ • v := Module.End.mem_eigenspace_iff.mp hv_mem
  have hv_orth : v ∈ Eᗮ := by
    have hCv : C v ∈ Eᗮ := by
      have hmem : C v ∈ LinearMap.range (Q : H →ₗ[𝕜] H) :=
        ⟨T (Q v), by simp [C]⟩
      rwa [Submodule.range_starProjection] at hmem
    have hv_eq : v = (μ⁻¹ : 𝕜) • C v := by
      rw [hvC, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    rw [hv_eq]
    exact Submodule.smul_mem _ _ hCv
  have hQv : Q v = v := Submodule.starProjection_eq_self_iff.mpr hv_orth
  have hTv_orth : T v ∈ Eᗮ :=
    orthogonalComplement_invariant hT hEinv v hv_orth
  have hQTv : Q (T v) = T v := Submodule.starProjection_eq_self_iff.mpr hTv_orth
  have hTv : T v = μ • v := by
    have h1 : C v = Q (T v) := by simp [C, hQv]
    rw [h1, hQTv] at hvC
    exact hvC
  have hμT : Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hTv, hv_ne⟩
  have hμε : ε ≤ ‖μ‖ := by rw [hμnorm]; exact le_of_lt hgt
  have hvE : v ∈ E := hEgen μ hμT hμε (Module.End.mem_eigenspace_iff.mpr hTv)
  have hvbot : v ∈ E ⊓ Eᗮ := ⟨hvE, hv_orth⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hvbot
  exact hv_ne ((Submodule.mem_bot 𝕜).mp hvbot)

/-- **Finite-rank approximation of compact self-adjoint operators.** For
every `ε > 0` there is a self-adjoint operator `F` of finite rank with
`‖T - F‖ ≤ ε`. -/
theorem exists_finiteRank_approx {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H →L[𝕜] H, IsSelfAdjoint F ∧
      FiniteDimensional 𝕜 ↥(LinearMap.range (F : H →ₗ[𝕜] H)) ∧ ‖T - F‖ ≤ ε := by
  classical
  have hfin := finite_eigenvalues_of_ge hT hc hε
  set s : Finset 𝕜 := hfin.toFinset with hsdef
  set E : Submodule 𝕜 H :=
    ⨆ μ ∈ s, Module.End.eigenspace (T : H →ₗ[𝕜] H) μ with hEdef
  have hmem_s : ∀ μ : 𝕜, μ ∈ s ↔
      Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧ ε ≤ ‖μ‖ := by
    intro μ
    rw [hsdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hEfin : FiniteDimensional 𝕜 ↥E := by
    rw [← Submodule.fg_iff_finiteDimensional]
    apply Submodule.fg_biSup s _ _
    intro μ hμ
    rw [Submodule.fg_iff_finiteDimensional]
    apply ContinuousLinearMap.finite_dimensional_eigenspace hc μ
    have hμS := (hmem_s μ).mp hμ
    intro hμ0
    rw [hμ0, norm_zero] at hμS
    exact absurd hμS.2 (not_le_of_gt hε)
  have : CompleteSpace ↥E := (Submodule.closed_of_finiteDimensional E).completeSpace_coe
  set P : H →L[𝕜] H := E.starProjection with hPdef
  set Q : H →L[𝕜] H := Eᗮ.starProjection with hQdef
  set F : H →L[𝕜] H := P ∘L T ∘L P with hFdef
  have hEinv : ∀ x ∈ E, T x ∈ E := by
    intro x hx
    have hmap := map_eigenspace_iSup_le (T := T) (s := s)
    have hxmap : (T : H →ₗ[𝕜] H) x ∈ Submodule.map (T : H →ₗ[𝕜] H) E :=
      Submodule.mem_map_of_mem hx
    exact hmap hxmap
  have hEgen : ∀ μ : 𝕜, Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ → ε ≤ ‖μ‖ →
      Module.End.eigenspace (T : H →ₗ[𝕜] H) μ ≤ E := by
    intro μ _hμ hμ
    have hμs : μ ∈ s := (hmem_s μ).mpr ⟨_hμ, hμ⟩
    refine le_trans
      (le_iSup (fun _ : μ ∈ s => Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) hμs) ?_
    exact le_iSup (fun ν => ⨆ _ : ν ∈ s, Module.End.eigenspace (T : H →ₗ[𝕜] H) ν) μ
  have hFsa : IsSelfAdjoint F := hT.conj_starProjection E
  have hFrange : LinearMap.range (F : H →ₗ[𝕜] H) ≤ E := by
    rintro y ⟨x, _, rfl⟩
    exact E.starProjection_apply_mem _
  have hFfin : FiniteDimensional 𝕜 ↥(LinearMap.range (F : H →ₗ[𝕜] H)) := by
    have : FiniteDimensional 𝕜 ↥E := hEfin
    exact Submodule.finiteDimensional_of_le hFrange
  have hnorm : ‖T - F‖ ≤ ε := by
    have hCbound : ‖Q ∘L T ∘L Q‖ ≤ ε :=
      norm_compression_le hT hc hε hEgen hEinv
    have h_op_eq : T - F = Q ∘L T ∘L Q := by
      ext x
      simp only [hFdef, sub_apply, ContinuousLinearMap.comp_apply]
      have hQx : Q x = x - P x := Submodule.starProjection_orthogonal_val x
      have hP_kill : ∀ y ∈ Eᗮ, P y = 0 := by
        intro y hy
        have hQy : Q y = y := Submodule.starProjection_eq_self_iff.mpr hy
        have hval := Submodule.starProjection_orthogonal_val (K := E) y
        rw [hQy] at hval
        -- hval : y = y - P y
        exact sub_eq_self.mp hval.symm
      have hQ_kill : ∀ z ∈ E, Q z = 0 := by
        intro z hz
        rw [Submodule.starProjection_orthogonal_val,
          Submodule.starProjection_eq_self_iff.mpr hz, sub_self]
      have h3 : P (T (P x)) = T (P x) :=
        Submodule.starProjection_eq_self_iff.mpr
          (hEinv _ (E.starProjection_apply_mem x))
      have h4 : P (T (x - P x)) = 0 :=
        hP_kill _ (orthogonalComplement_invariant hT hEinv _
          (Submodule.sub_starProjection_mem_orthogonal x))
      have h5 : P (T x) = T (P x) := by
        have hdecomp : T x = T (P x) + T (x - P x) := by
          rw [← map_add]
          congr 1
          exact (add_sub_cancel _ _).symm
        rw [hdecomp, map_add, h3, h4, add_zero]
      rw [hQx, map_sub, map_sub,
        Submodule.starProjection_orthogonal_val (T x),
        hQ_kill _ (hEinv _ (E.starProjection_apply_mem x)), sub_zero, h5, h3]
    rw [h_op_eq]
    exact hCbound
  exact ⟨F, hFsa, hFfin, hnorm⟩

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteRankApprox
