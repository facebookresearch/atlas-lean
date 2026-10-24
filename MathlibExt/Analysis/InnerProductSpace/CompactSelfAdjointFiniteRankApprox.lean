/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Sequences

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
ported here; the statement below is proved from scratch. It is genuinely new
against the existing library: Mathlib has the norm-attained eigenvalue, the
finiteness of each nonzero eigenspace, and the spectral decomposition, but
no finite-rank approximation theorem for compact operators, and MathlibExt
has no finite-rank approximation for compact self-adjoint operators either
(its `CompactSpectral.compactNormal_hilbertBasis` is `ℂ`-only, assumes
normality, and gives a Hilbert basis rather than a norm approximation).

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.compact_selfAdjoint_maximum_principle` and
`SpectralTheory.spectral_theorem_range_decomposition`
(Theorem (Maximum principle) and Theorem (Spectral theorem), May 11, 2021).
The full ordered eigenvalue sequence of the maximum principle is not proved
here, only the finite-rank approximation above.
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

/-- **A nonzero compact self-adjoint operator has an eigenvalue of norm
`‖T‖`.** -/
private theorem exists_hasEigenvalue_norm_eq (T : H →L[𝕜] H) (hT : IsSelfAdjoint T)
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

/-- **Finiteness of eigenvalues bounded away from zero.** For a compact
self-adjoint operator `T` and any `ε > 0`, the set of eigenvalues `μ` of `T`
with `ε ≤ ‖μ‖` is finite. -/
private theorem finite_eigenvalues_of_ge {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : 𝕜 | Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧ ε ≤ ‖μ‖} := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set e := hinf.natEmbedding with hedef
  have ha : ∀ n, Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) ((e n : 𝕜)) ∧
      ε ≤ ‖(e n : 𝕜)‖ := fun n => (e n).2
  have hinj : Function.Injective (fun n => ((e n : 𝕜))) := by
    intro m n hmn
    exact e.injective (Subtype.ext hmn)
  have hex : ∀ n, ∃ x : H, T x = ((e n : 𝕜)) • x ∧ ‖x‖ = 1 := by
    intro n
    obtain ⟨x, hx_mem, hx_ne⟩ := (ha n).1.exists_hasEigenvector
    have hxT : T x = ((e n : 𝕜)) • x := Module.End.mem_eigenspace_iff.mp hx_mem
    refine ⟨(((‖x‖⁻¹ : ℝ)) : 𝕜) • x, ?_, ?_⟩
    · rw [map_smul, hxT]
      exact (smul_comm _ _ _).symm
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx_ne)]
  choose u hu_eig hu_norm using hex
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have horth : ∀ m n, m ≠ n → @inner 𝕜 H _ (u m) (u n) = 0 := by
    intro m n hmn
    have hne : ((e m : 𝕜)) ≠ ((e n : 𝕜)) := fun hcon => hmn (hinj hcon)
    exact hsym.orthogonalFamily_eigenspaces hne
      ⟨u m, Module.End.mem_eigenspace_iff.mpr (hu_eig m)⟩
      ⟨u n, Module.End.mem_eigenspace_iff.mpr (hu_eig n)⟩
  have hsep : ∀ m n, m ≠ n → ε ≤ ‖T (u m) - T (u n)‖ := by
    intro m n hmn
    have h1 : T (u m) - T (u n)
        = ((e m : 𝕜)) • (u m) - ((e n : 𝕜)) • (u n) := by
      rw [hu_eig m, hu_eig n]
    have hort : @inner 𝕜 H _ (((e m : 𝕜)) • (u m)) (((e n : 𝕜)) • (u n)) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth m n hmn, mul_zero, mul_zero]
    have hpyth : ‖T (u m) - T (u n)‖ ^ 2
        = ‖((e m : 𝕜))‖ ^ 2 + ‖((e n : 𝕜))‖ ^ 2 := by
      have hnorm : ‖((e m : 𝕜)) • (u m) - ((e n : 𝕜)) • (u n)‖ ^ 2
          = ‖((e m : 𝕜)) • (u m)‖ ^ 2
            - 2 * RCLike.re (@inner 𝕜 H _ (((e m : 𝕜)) • (u m)) (((e n : 𝕜)) • (u n)))
            + ‖((e n : 𝕜)) • (u n)‖ ^ 2 :=
        norm_sub_sq _ _
      rw [h1, hnorm, hort]
      simp [norm_smul, hu_norm m, hu_norm n]
    have hge : ε ^ 2 ≤ ‖T (u m) - T (u n)‖ ^ 2 := by
      rw [hpyth]
      have hm := (ha m).2
      have hn := (ha n).2
      nlinarith [sq_nonneg (‖((e m : 𝕜))‖ - ε), sq_nonneg (‖((e n : 𝕜))‖ - ε),
        sq_nonneg ‖((e m : 𝕜))‖, sq_nonneg ‖((e n : 𝕜))‖]
    have hnn : (0 : ℝ) ≤ ‖T (u m) - T (u n)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖T (u m) - T (u n)‖ - ε), hge, hnn, hε]
  have hcompact := hc.isCompact_closure_image_closedBall (1 : ℝ)
  have hmem : ∀ n, T (u n)
      ∈ closure (⇑T '' Metric.closedBall (0 : H) 1) := by
    intro n
    apply subset_closure
    refine ⟨u n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hu_norm n]
  obtain ⟨L, -, φ, hmono, hlim⟩ := hcompact.tendsto_subseq hmem
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 2) (by linarith)
  have h1 := hN (N + 1) (Nat.le_succ N) N (le_refl N)
  simp only [Function.comp_apply] at h1
  have h2 : ε ≤ dist (T (u (φ (N + 1)))) (T (u (φ N))) := by
    rw [dist_eq_norm]
    apply hsep
    exact ne_of_gt (hmono (Nat.lt_succ_self N))
  linarith

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
