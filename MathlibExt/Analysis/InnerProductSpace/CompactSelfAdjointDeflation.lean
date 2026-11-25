/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalue

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

open ContinuousLinearMap InnerProductSpace
open scoped ComplexConjugate

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointDeflation

/-!
# Deflation: the next eigenvalue of a compact self-adjoint operator

This is the inductive step of the maximum principle for compact self-adjoint
operators (the book's Theorem (Maximum principle), May 11, 2021 section),
which orders the nonzero eigenvalues by decreasing modulus. The full
ordered eigenvalue sequence is not proved here. Instead, this file proves
the step that produces the *next* eigenvalue: given a finite family of
eigenvectors, compress `T` by the orthogonal projection `P` onto the
orthogonal complement `S` of their span, and apply the first-step argument
(norm-attained eigenvalue) to the compression `P ∘L T ∘L P`. The resulting
eigenvector lies in `S`, is an eigenvector of `T` itself, and its eigenvalue
is maximal among Rayleigh quotients on `S`.

The first-step argument is supplied by
`CompactSelfAdjointNormEigenvalue.exists_unit_eigenvector_real_eigenvalue`.
The public content here is the deflation step, which is not in Mathlib
(Mathlib has the compression's self-adjointness as
`IsSelfAdjoint.conj_starProjection`, but no eigenvalue conclusion for it)
and not in any earlier batch (Batches 11-13 proved the first step, the
range decomposition, and finiteness of eigenvalues above `ε`).

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.compact_selfAdjoint_maximum_principle`
(Theorem (Maximum principle), May 11, 2021). The v1 formalization is left
unproved; it is not ported. The statements below are proved from scratch.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Deflation step.** Let $T$ be a compact self-adjoint operator on a Hilbert space $H$ over
$\mathbb{R}$ or $\mathbb{C}$, let $S$ be a linear subspace of $H$ that admits an orthogonal
projection $P : H \to H$ onto $S$ and satisfies $T(S) \subseteq S$, and let $T_1 = PTP$ be the
compression of $T$ to $S$. If $T_1 \neq 0$, then there are a real number $r$ and a unit vector
$v \in S$ with $Tv = rv$, $|r| = \|T_1\|$ and $|r| \le \|T\|$. -/
theorem exists_next_eigenvector_of_invariant {S : Submodule 𝕜 H} [S.HasOrthogonalProjection]
    {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hS : ∀ x ∈ S, T x ∈ S)
    (hT₁ : S.starProjection ∘L T ∘L S.starProjection ≠ 0) :
    ∃ r : ℝ, ∃ v : H, ‖v‖ = 1 ∧ v ∈ S ∧ T v = (r : 𝕜) • v ∧
      |r| = ‖S.starProjection ∘L T ∘L S.starProjection‖ ∧ |r| ≤ ‖T‖ := by
  set P : H →L[𝕜] H := S.starProjection with hP
  set T₁ : H →L[𝕜] H := P ∘L T ∘L P with hT₁def
  have hT₁sa : IsSelfAdjoint T₁ := hT.conj_starProjection S
  have hT₁c : IsCompactOperator (T₁ : H → H) := by
    have h1 : IsCompactOperator ((T ∘L P : H →L[𝕜] H) : H → H) := by
      have h := hc.comp_clm (P : H →L[𝕜] H)
      simpa [ContinuousLinearMap.coe_comp] using h
    have h2 : IsCompactOperator ((P ∘L (T ∘L P) : H →L[𝕜] H) : H → H) := by
      have h := h1.clm_comp (P : H →L[𝕜] H)
      simpa [ContinuousLinearMap.coe_comp, Function.comp_assoc] using h
    simpa [hT₁def, hP, ContinuousLinearMap.comp_assoc] using h2
  have hT₁0 : T₁ ≠ 0 := hT₁
  obtain ⟨r, v, hv_norm, hv_eig, hr⟩ :=
    CompactSelfAdjointNormEigenvalue.exists_unit_eigenvector_real_eigenvalue
      T₁ hT₁sa hT₁c hT₁0
  have hr0 : r ≠ 0 := by
    intro hrr
    rw [hrr] at hr
    simp at hr
    exact hT₁0 (norm_eq_zero.mp hr.symm)
  have hr0' : (r : 𝕜) ≠ 0 := by exact_mod_cast hr0
  -- The eigenvector `v` of `T₁` lies in `S`: `T₁ v` lies in the range of the
  -- projection, and `v = r⁻¹ • (T₁ v)`.
  have hvS : v ∈ S := by
    have hmem : T₁ v ∈ S := by
      have h1 : T₁ v ∈ LinearMap.range (P : H →L[𝕜] H).toLinearMap := by
        refine ⟨T (P v), ?_⟩
        simp [hT₁def, ContinuousLinearMap.comp_apply]
      rwa [Submodule.range_starProjection] at h1
    have hrv : (r : 𝕜) • v ∈ S := by rw [← hv_eig]; exact hmem
    have h2 : v = ((r : 𝕜)⁻¹) • ((r : 𝕜) • v) := (inv_smul_smul₀ hr0' v).symm
    rw [h2]
    exact S.smul_mem _ hrv
  have hPv : P v = v := by
    rw [hP]
    exact Submodule.starProjection_eq_self_iff.mpr hvS
  have hTvS : T v ∈ S := hS v hvS
  have hT₁v : T₁ v = T v := by
    have e1 : T₁ v = P (T (P v)) := by simp [hT₁def]
    rw [e1, hPv]
    exact Submodule.starProjection_eq_self_iff.mpr hTvS
  refine ⟨r, v, hv_norm, hvS, ?_, ?_, ?_⟩
  · rw [← hT₁v]; exact hv_eig
  · exact hr
  · rw [hr]
    calc ‖T₁‖ = ‖P ∘L T ∘L P‖ := by rw [hT₁def]
      _ ≤ ‖P‖ * ‖T‖ * ‖P‖ := by
          have h1 : ‖T ∘L P‖ ≤ ‖T‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le _ _
          have h2 : ‖P ∘L (T ∘L P)‖ ≤ ‖P‖ * ‖T ∘L P‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          have h3 : (P ∘L T ∘L P : H →L[𝕜] H) = P ∘L (T ∘L P) := rfl
          rw [h3]
          calc ‖P ∘L (T ∘L P)‖ ≤ ‖P‖ * ‖T ∘L P‖ := h2
            _ ≤ ‖P‖ * (‖T‖ * ‖P‖) :=
                mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
            _ = ‖P‖ * ‖T‖ * ‖P‖ := (mul_assoc _ _ _).symm
      _ ≤ 1 * ‖T‖ * 1 := by
          have hPle : ‖P‖ ≤ 1 := by rw [hP]; exact Submodule.starProjection_norm_le S
          have hnn : 0 ≤ ‖T‖ := norm_nonneg _
          have h1 : ‖P‖ * ‖T‖ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right hPle hnn
          have h2 : ‖P‖ * ‖T‖ * ‖P‖ ≤ 1 * ‖T‖ * ‖P‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          calc ‖P‖ * ‖T‖ * ‖P‖ ≤ 1 * ‖T‖ * ‖P‖ := h2
            _ ≤ 1 * ‖T‖ * 1 := by
                exact mul_le_mul_of_nonneg_left hPle (by positivity)
      _ = ‖T‖ := by simp

/-- **Next eigenvalue after a finite family of eigenvectors.** Let $T$ be a compact self-adjoint
operator on a Hilbert space $H$ over $\mathbb{R}$ or $\mathbb{C}$, let $u_1, \dots, u_n \in H$ and
scalars $\mu_1, \dots, \mu_n$ satisfy $T u_i = \mu_i u_i$ for every $i$, and let $S$ be the
orthogonal complement of the span of $u_1, \dots, u_n$. If $Tz \neq 0$ for some $z \in S$, then
there are a real number $r$ and a unit vector $v$ with $\langle v, u_i \rangle = 0$ for every $i$,
$Tv = rv$ and $\langle Tv, v \rangle = r$, such that $|\langle Tx, x \rangle| \le |r|$ for
every unit vector $x \in S$. In particular $v \in S$, so $|r|$ is the maximum of
$|\langle Tx, x \rangle|$ over unit vectors $x \in S$.

The vectors $u_i$ need not be orthonormal, or even nonzero. -/
theorem exists_next_eigenvector_of_finite_eigenvectors
    {n : ℕ} {u : Fin n → H} {μ : Fin n → 𝕜} {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hμ : ∀ i, T (u i) = μ i • u i)
    (hne : ∃ z ∈ (Submodule.span 𝕜 (Set.range u))ᗮ, T z ≠ 0) :
    ∃ r : ℝ, ∃ v : H,
      ‖v‖ = 1 ∧
      (∀ i, ⟪v, u i⟫_𝕜 = 0) ∧
      T v = (r : 𝕜) • v ∧
      (∀ x ∈ (Submodule.span 𝕜 (Set.range u))ᗮ, ‖x‖ = 1 →
        ‖⟪T x, x⟫_𝕜‖ ≤ |r|) ∧
      ⟪T v, v⟫_𝕜 = (r : 𝕜) := by
  set K : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range u) with hK
  set S : Submodule 𝕜 H := Kᗮ with hSdef
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hKinv : ∀ y ∈ K, T y ∈ K := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        rw [hμ i]
        exact Submodule.smul_mem K _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem K _ hx
  have hS : ∀ x ∈ S, T x ∈ S := by
    intro x hx
    rw [hSdef, Submodule.mem_orthogonal']
    intro y hy
    calc ⟪T x, y⟫_𝕜 = ⟪x, ContinuousLinearMap.adjoint T y⟫_𝕜 :=
          (ContinuousLinearMap.adjoint_inner_right T x y).symm
      _ = ⟪x, T y⟫_𝕜 := by rw [hT.adjoint_eq]
      _ = 0 := Submodule.inner_left_of_mem_orthogonal (hKinv y hy) hx
  have hT₁ : S.starProjection ∘L T ∘L S.starProjection ≠ 0 := by
    intro h0
    obtain ⟨z, hzS, hzT⟩ := hne
    have hz1 : (S.starProjection ∘L T ∘L S.starProjection) z = 0 := by
      rw [h0]; simp
    simp only [ContinuousLinearMap.comp_apply] at hz1
    rw [Submodule.starProjection_eq_self_iff.mpr hzS,
      Submodule.starProjection_eq_self_iff.mpr (hS z hzS)] at hz1
    exact hzT hz1
  obtain ⟨r, v, hv_norm, hvS, hv_eig, hr_norm, _hr_le⟩ :=
    exists_next_eigenvector_of_invariant hT hc hS hT₁
  refine ⟨r, v, hv_norm, ?_, hv_eig, ?_, ?_⟩
  · intro i
    exact Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self i)) hvS
  · intro x hxS hx1
    have hT₁x : (S.starProjection ∘L T ∘L S.starProjection) x = T x := by
      have e1 : (S.starProjection ∘L T ∘L S.starProjection) x
          = S.starProjection (T (S.starProjection x)) := by
        simp [ContinuousLinearMap.comp_apply]
      rw [e1, Submodule.starProjection_eq_self_iff.mpr hxS,
        Submodule.starProjection_eq_self_iff.mpr (hS x hxS)]
    have hle : |(S.starProjection ∘L T ∘L S.starProjection).rayleighQuotient x|
        ≤ ‖S.starProjection ∘L T ∘L S.starProjection‖ :=
      (S.starProjection ∘L T ∘L S.starProjection).rayleighQuotient_le_norm x
    have hRQ : (S.starProjection ∘L T ∘L S.starProjection).rayleighQuotient x
        = RCLike.re ⟪T x, x⟫_𝕜 := by
      show (S.starProjection ∘L T ∘L S.starProjection).reApplyInnerSelf x / ‖x‖ ^ 2 = _
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, hT₁x, hx1]
      simp
    have hnorm_inner : ‖⟪T x, x⟫_𝕜‖ = |RCLike.re ⟪T x, x⟫_𝕜| := by
      have hreal : ⟪T x, x⟫_𝕜 = (RCLike.re ⟪T x, x⟫_𝕜 : 𝕜) := by
        have h1 := hsym.coe_reApplyInnerSelf_apply x
        rw [ContinuousLinearMap.reApplyInnerSelf_apply] at h1
        exact h1.symm
      conv_lhs => rw [hreal]
      rw [RCLike.norm_ofReal]
    rw [hnorm_inner, ← hRQ, hr_norm]
    exact hle
  · calc ⟪T v, v⟫_𝕜 = ⟪(r : 𝕜) • v, v⟫_𝕜 := by rw [hv_eig]
      _ = (r : 𝕜) := by
          rw [inner_smul_left, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K,
            hv_norm]
          simp

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointDeflation
