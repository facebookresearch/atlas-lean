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

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple

/-!
# Maximum principle for compact self-adjoint operators

A compact self-adjoint operator `T` on an infinite-dimensional Hilbert space
has its nonzero eigenvalues ordered as `|λ₁| ≥ |λ₂| ≥ ⋯` (counted with
multiplicity), with pairwise orthonormal eigenvectors `uₖ` and
`|λₖ| → 0`. Each `|λₖ|` is the maximum of `‖⟪T x, x⟫‖` over unit vectors
`x` orthogonal to `u₁, …, uₖ₋₁`, attained at `uₖ`. This is the book's
Theorem (Maximum principle), May 11, 2021 section.

The proof iterates the deflation step: at each stage, compress `T` to the
orthogonal complement of the span of the eigenvectors found so far and apply
the first-step argument (a nonzero compact self-adjoint operator has a unit
eigenvector whose real eigenvalue has absolute value equal to the norm).
The `|λₖ| → 0` conclusion uses that only finitely many eigenvalues can lie
above any `ε > 0` (a compactness / separation argument), so an infinite
orthonormal eigenvector sequence with `|λₖ| ≥ ε` would give an infinite
orthonormal family inside a finite-dimensional eigenspace.

The v1 formalization of this theorem
(`SpectralTheory.compact_selfAdjoint_maximum_principle`) is left unproved
(left unproved in v1) and is not ported; the statement below is proved from scratch.
Earlier batches proved only pieces of it: the first-step eigenvalue, the
finiteness of eigenvalues above `ε`, the deflation step, and the finite-rank
approximation. The private helpers below re-prove the first-step and
finiteness arguments in this file, since the batches are parallel stacks on
the same base and cannot import each other. Two adaptations to the v1
statement: the eigenvalues are stated as reals (those of a self-adjoint
operator are real), and the variational formula is stated in its
maximality-plus-attained form rather than as a `⨆` over binders, which is
equivalent (the set of Rayleigh quotients over the unit vectors orthogonal
to the previous eigenvectors is bounded above and attains its bound).

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.compact_selfAdjoint_maximum_principle`
(Theorem (Maximum principle), May 11, 2021 section).
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

/-- **The norm of a compact self-adjoint operator is a real eigenvalue,
attained at a unit vector.** If `T ≠ 0` is compact and self-adjoint,
there are `r : ℝ` and a unit vector `u` with `T u = r • u` and `|r| = ‖T‖`. -/
private theorem exists_unit_eigenvector_real_eigenvalue (T : H →L[𝕜] H)
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H)) (hT0 : T ≠ 0) :
    ∃ r : ℝ, ∃ u : H, ‖u‖ = 1 ∧ T u = (r : 𝕜) • u ∧ |r| = ‖T‖ := by
  obtain ⟨μ, _hμ0, hnorm, heig⟩ := exists_hasEigenvalue_norm_eq T hT hc hT0
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hconj : conj μ = μ := hsym.conj_eigenvalue_eq_self heig
  have hμreal : (RCLike.re μ : 𝕜) = μ := RCLike.conj_eq_iff_re.mp hconj
  obtain ⟨u₀, hu₀mem, hu₀ne⟩ := heig.exists_hasEigenvector
  have hu₀T : T u₀ = μ • u₀ := Module.End.mem_eigenspace_iff.mp hu₀mem
  have hu₀norm : ‖u₀‖ ≠ 0 := norm_ne_zero_iff.mpr hu₀ne
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

/-- **Finiteness of eigenvalues bounded away from zero.** For a compact
self-adjoint operator `T` and any `ε > 0`, the set of eigenvalues `μ` of `T`
with `ε ≤ ‖μ‖` is finite. The proof is a compactness argument: unit
eigenvectors for distinct eigenvalues are orthogonal, so their images under
`T` are `ε`-separated, contradicting relative compactness of the image of
the unit ball. -/
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

/-- **Deflation on an invariant subspace, with maximality.** Let `S` be
invariant under a compact self-adjoint `T`, and suppose the compression
`P ∘L T ∘L P` of `T` to `S` is nonzero. Then there is a real eigenvalue
`r` and a unit eigenvector `v ∈ S` for `T`, such that `|r|` is the maximum
of `‖⟪T x, x⟫‖` over unit vectors `x ∈ S`. -/
private theorem exists_next_eigenvector_of_invariant_max {S : Submodule 𝕜 H}
    [S.HasOrthogonalProjection] {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hS : ∀ x ∈ S, T x ∈ S)
    (hT₁ : S.starProjection ∘L T ∘L S.starProjection ≠ 0) :
    ∃ r : ℝ, ∃ v : H, ‖v‖ = 1 ∧ v ∈ S ∧ T v = (r : 𝕜) • v ∧
      (∀ x ∈ S, ‖x‖ = 1 → ‖⟪T x, x⟫_𝕜‖ ≤ |r|) := by
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
  obtain ⟨r, v, hv_norm, hv_eig, hr⟩ :=
    exists_unit_eigenvector_real_eigenvalue T₁ hT₁sa hT₁c hT₁
  have hr0 : r ≠ 0 := by
    intro hrr
    rw [hrr] at hr
    simp at hr
    exact hT₁ (norm_eq_zero.mp hr.symm)
  have hr0' : (r : 𝕜) ≠ 0 := by exact_mod_cast hr0
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
  have hPv : P v = v := Submodule.starProjection_eq_self_iff.mpr hvS
  have hTvS : T v ∈ S := hS v hvS
  have hT₁v : T₁ v = T v := by
    have e1 : T₁ v = P (T (P v)) := by simp [hT₁def]
    rw [e1, hPv]
    exact Submodule.starProjection_eq_self_iff.mpr hTvS
  have hTv : T v = (r : 𝕜) • v := by rw [← hT₁v]; exact hv_eig
  refine ⟨r, v, hv_norm, hvS, hTv, ?_⟩
  intro x hxS hx1
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
    have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
    have hreal : ⟪T x, x⟫_𝕜 = (RCLike.re ⟪T x, x⟫_𝕜 : 𝕜) := by
      have h1 := hsym.coe_reApplyInnerSelf_apply x
      rw [ContinuousLinearMap.reApplyInnerSelf_apply] at h1
      exact h1.symm
    conv_lhs => rw [hreal]
    rw [RCLike.norm_ofReal]
  rw [hnorm_inner, ← hRQ, hr]
  exact hle

/-- The step properties for a candidate pair `p` after the partial
assignment `f` at stage `n`: `p` is a unit eigenvector, orthogonal to all
previous vectors, and maximal among Rayleigh quotients over unit vectors
orthogonal to all previous vectors. -/
private def NextProps (T : H →L[𝕜] H) (f : ℕ → ℝ × H) (n : ℕ) (p : ℝ × H) : Prop :=
  ‖p.2‖ = 1 ∧ T p.2 = (p.1 : 𝕜) • p.2 ∧
  (∀ j < n, ⟪p.2, (f j).2⟫_𝕜 = 0) ∧
  (∀ x : H, ‖x‖ = 1 → (∀ j < n, ⟪x, (f j).2⟫_𝕜 = 0) → ‖⟪T x, x⟫_𝕜‖ ≤ |p.1|)

/-- The accumulated step properties of an assignment `f` at index `i`:
the `i`-th pair is a unit eigenvector, orthogonal to all earlier pairs, and
maximal among Rayleigh quotients over unit vectors orthogonal to all earlier
pairs. -/
private def StepProps (T : H →L[𝕜] H) (f : ℕ → ℝ × H) (i : ℕ) : Prop :=
  ‖(f i).2‖ = 1 ∧ T (f i).2 = ((f i).1 : 𝕜) • (f i).2 ∧
  (∀ j < i, ⟪(f i).2, (f j).2⟫_𝕜 = 0) ∧
  (∀ x : H, ‖x‖ = 1 → (∀ j < i, ⟪x, (f j).2⟫_𝕜 = 0) → ‖⟪T x, x⟫_𝕜‖ ≤ |(f i).1|)

omit [CompleteSpace H] in
/-- Step properties only mention indices `≤ i`, so they are preserved by
changing the assignment at indices `> i`. -/
private theorem stepProps_congr {T : H →L[𝕜] H} {f g : ℕ → ℝ × H} {i : ℕ}
    (h : ∀ j ≤ i, f j = g j) (hf : StepProps T f i) : StepProps T g i := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h i le_rfl]; exact h1
  · rw [← h i le_rfl]; exact h2
  · intro j hj
    rw [← h i le_rfl, ← h j (le_of_lt hj)]
    exact h3 j hj
  · intro x hx1 hxorth
    rw [← h i le_rfl]
    apply h4 x hx1
    intro j hj
    have hgj := hxorth j hj
    rw [← h j (le_of_lt hj)] at hgj
    exact hgj

omit [CompleteSpace H] in
/-- Step properties for the updated assignment at the updated index are
exactly the next-pair properties. -/
private theorem stepProps_update_self {T : H →L[𝕜] H} {f : ℕ → ℝ × H} {n : ℕ}
    {p : ℝ × H} (hp : NextProps T f n p) :
    StepProps T (Function.update f n p) n := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Function.update_self]; exact h1
  · simp only [Function.update_self]; exact h2
  · intro j hj
    rw [Function.update_self, Function.update_of_ne (ne_of_lt hj)]
    exact h3 j hj
  · intro x hx1 hxorth
    rw [Function.update_self]
    apply h4 x hx1
    intro j hj
    have hgj := hxorth j hj
    rw [Function.update_of_ne (ne_of_lt hj)] at hgj
    exact hgj

set_option linter.style.haveILetI false in
/-- There is always a next pair: either `T` does not vanish on the
orthogonal complement of the span of the previous eigenvectors, and the
deflation step applies, or `T` vanishes there, and any unit vector in the
orthogonal complement (which exists because `H` is infinite-dimensional)
works with eigenvalue `0`. -/
private theorem exists_next_pair {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    {n : ℕ} {f : ℕ → ℝ × H} (hf : ∀ i < n, StepProps T f i) :
    ∃ p : ℝ × H, NextProps T f n p := by
  classical
  set u : Fin n → H := fun i => (f i.1).2 with hu
  set K : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range u) with hK
  have hmemK : ∀ j < n, (f j).2 ∈ K := by
    intro j hj
    apply Submodule.subset_span
    exact ⟨⟨j, hj⟩, rfl⟩
  have hKinv : ∀ y ∈ K, T y ∈ K := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        rw [(hf i.1 i.2).2.1]
        exact Submodule.smul_mem K _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem K _ hx
  have hSinv : ∀ v ∈ Kᗮ, T v ∈ Kᗮ := orthogonalComplement_invariant hT hKinv
  have hxS : ∀ x : H, (∀ j < n, ⟪x, (f j).2⟫_𝕜 = 0) → x ∈ Kᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal']
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact hx i.1 i.2
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul a a' _ ha => rw [inner_smul_right, ha, mul_zero]
  have hKfin : FiniteDimensional 𝕜 ↥K :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  have : CompleteSpace ↥K := (Submodule.closed_of_finiteDimensional K).completeSpace_coe
  have : CompleteSpace ↥Kᗮ := (Submodule.isClosed_orthogonal K).completeSpace_coe
  by_cases hne : ∃ z ∈ Kᗮ, T z ≠ 0
  · have hT₁ : Kᗮ.starProjection ∘L T ∘L Kᗮ.starProjection ≠ 0 := by
      intro h0
      obtain ⟨z, hzS, hzT⟩ := hne
      have hz1 : (Kᗮ.starProjection ∘L T ∘L Kᗮ.starProjection) z = 0 := by
        rw [h0]; simp
      simp only [ContinuousLinearMap.comp_apply] at hz1
      rw [Submodule.starProjection_eq_self_iff.mpr hzS,
        Submodule.starProjection_eq_self_iff.mpr (hSinv z hzS)] at hz1
      exact hzT hz1
    obtain ⟨r, v, hv_norm, hvS, hv_eig, hmax⟩ :=
      exists_next_eigenvector_of_invariant_max hT hc hSinv hT₁
    refine ⟨(r, v), hv_norm, hv_eig, ?_, ?_⟩
    · intro j hj
      exact Submodule.inner_left_of_mem_orthogonal (hmemK j hj) hvS
    · intro x hx1 hxorth
      exact hmax x (hxS x hxorth) hx1
  · push Not at hne
    have hS_ne : Kᗮ ≠ ⊥ := by
      intro hS0
      have hKtop : K = ⊤ := by
        have h1 : K.topologicalClosure = ⊤ := by
          have h2 : Kᗮᗮ = (⊥ : Submodule 𝕜 H)ᗮ := by rw [hS0]
          rw [Submodule.orthogonal_orthogonal_eq_closure] at h2
          rw [h2]
          simp
        rw [← (Submodule.closed_of_finiteDimensional K).submodule_topologicalClosure_eq]
        exact h1
      have hfinH : FiniteDimensional 𝕜 H := by
        have h2 : FiniteDimensional 𝕜 ↥(⊤ : Submodule 𝕜 H) := by
          rw [← hKtop]; exact hKfin
        haveI := h2
        exact LinearEquiv.finiteDimensional Submodule.topEquiv
      exact hInf hfinH
    obtain ⟨w, hwS, hwne⟩ := (Submodule.ne_bot_iff _).mp hS_ne
    set c : 𝕜 := ((‖w‖⁻¹ : ℝ) : 𝕜) with hc_def
    refine ⟨(0, c • w), ?_, ?_, ?_, ?_⟩
    · rw [norm_smul, hc_def, RCLike.norm_ofReal,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), inv_mul_cancel₀
        (norm_ne_zero_iff.mpr hwne)]
    · have hvS : c • w ∈ Kᗮ := Submodule.smul_mem Kᗮ _ hwS
      have h0 : T (c • w) = 0 := by
        rw [map_smul, hne w hwS, smul_zero]
      rw [h0]
      simp
    · intro j hj
      have hvS : c • w ∈ Kᗮ := Submodule.smul_mem Kᗮ _ hwS
      exact Submodule.inner_left_of_mem_orthogonal (hmemK j hj) hvS
    · intro x hx1 hxorth
      have hxS' := hxS x hxorth
      have hTx : T x = 0 := hne x hxS'
      rw [hTx]
      simp

omit [CompleteSpace H] in
private theorem nextPair_exists {T : H →L[𝕜] H} (f : ℕ → ℝ × H) (n : ℕ) :
    ∃ p : ℝ × H, NextProps T f n p ∨ ¬ ∃ p', NextProps T f n p' := by
  by_cases h : ∃ p, NextProps T f n p
  · obtain ⟨p, hp⟩ := h; exact ⟨p, Or.inl hp⟩
  · exact ⟨(0, 0), Or.inr h⟩

/-- The next pair chosen at stage `n` for the partial assignment `f`:
the chosen next pair if one exists (it always does, by
`exists_next_pair`), else `(0, 0)`. -/
private noncomputable def nextPair {T : H →L[𝕜] H} (_hT : IsSelfAdjoint T)
    (_hc : IsCompactOperator (T : H → H)) (_hInf : ¬ FiniteDimensional 𝕜 H)
    (f : ℕ → ℝ × H) (n : ℕ) : ℝ × H :=
  Classical.choose (nextPair_exists (T := T) f n)

/-- The chosen next pair always satisfies the next-pair properties. -/
private theorem nextPair_props {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    {n : ℕ} {f : ℕ → ℝ × H} (hf : ∀ i < n, StepProps T f i) :
    NextProps T f n (nextPair hT hc hInf f n) := by
  have hex : ∃ p, NextProps T f n p := exists_next_pair hT hc hInf hf
  have hspec : NextProps T f n (nextPair hT hc hInf f n) ∨
      ¬ ∃ p', NextProps T f n p' :=
    Classical.choose_spec (nextPair_exists (T := T) f n)
  rcases hspec with h | h
  · exact h
  · exact absurd hex h

/-- The partial assignments built by the iteration: `seqF n` is the
assignment after `n` steps, with the first `n` pairs fixed. -/
private noncomputable def seqF {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H) :
    ℕ → (ℕ → ℝ × H)
  | 0 => fun _ => (0, 0)
  | (n + 1) => Function.update (seqF hT hc hInf n) n
      (nextPair hT hc hInf (seqF hT hc hInf n) n)

/-- The assignment after `n` steps satisfies the step properties at every
index `< n`. -/
private theorem seqF_valid {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    (n : ℕ) : ∀ i < n, StepProps T (seqF hT hc hInf n) i := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro i hi
      by_cases hin : i = n
      · subst hin
        apply stepProps_update_self
        exact nextPair_props hT hc hInf ih
      · have hi' : i < n := by omega
        apply stepProps_congr _ (ih i hi')
        intro j hj
        have hj' : j ≠ n := by omega
        simp [seqF, Function.update_of_ne hj']

/-- The assignments stabilize below the number of steps taken. -/
private theorem seqF_stable {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    {i n m : ℕ} (hi : i < n) (hnm : n ≤ m) :
    seqF hT hc hInf m i = seqF hT hc hInf n i := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      simp only [seqF, Function.update_of_ne (show i ≠ m from by omega)]
      exact ih


/-- The `n`-th eigenvalue in the ordered sequence: the `n`-th pair built by
the iteration. -/
private noncomputable def eigSeq {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    (n : ℕ) : ℝ :=
  (seqF hT hc hInf (n + 1) n).1

/-- The `n`-th eigenvector in the ordered sequence. -/
private noncomputable def eigVec {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    (n : ℕ) : H :=
  (seqF hT hc hInf (n + 1) n).2

/-- Every index of the eigenvalue/eigenvector sequence satisfies the step
properties. -/
private theorem stepProps_eig {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    (i : ℕ) :
    StepProps T (fun j => (eigSeq hT hc hInf j, eigVec hT hc hInf j)) i := by
  apply stepProps_congr _ (seqF_valid hT hc hInf (i + 1) i (Nat.lt_succ_self i))
  intro j hj
  show seqF hT hc hInf (i + 1) j = (eigSeq hT hc hInf j, eigVec hT hc hInf j)
  rw [seqF_stable hT hc hInf (Nat.lt_succ_self j) (show j + 1 ≤ i + 1 from by omega)]
  exact Prod.mk.eta.symm

/-- The eigenvectors in the ordered sequence are orthonormal. -/
private theorem orthonormal_eigVec {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H) :
    Orthonormal 𝕜 (eigVec hT hc hInf) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K, (stepProps_eig hT hc hInf i).1]
    simp
  · rw [ite_eq_right hij]
    rcases lt_or_gt_of_ne hij with h | h
    · have h2 : ⟪eigVec hT hc hInf j, eigVec hT hc hInf i⟫_𝕜 = 0 :=
        (stepProps_eig hT hc hInf j).2.2.1 i h
      rw [← inner_conj_symm, h2, map_zero]
    · exact (stepProps_eig hT hc hInf i).2.2.1 j h

/-- The Rayleigh quotient attains `|λₙ|` at the `n`-th eigenvector. -/
private theorem rayleigh_at_eigVec {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H)
    (n : ℕ) :
    ‖⟪T (eigVec hT hc hInf n), eigVec hT hc hInf n⟫_𝕜‖ = |eigSeq hT hc hInf n| := by
  have hT' := (stepProps_eig hT hc hInf n).2.1
  have hn1 := (stepProps_eig hT hc hInf n).1
  calc ‖⟪T (eigVec hT hc hInf n), eigVec hT hc hInf n⟫_𝕜‖
      = ‖⟪(eigSeq hT hc hInf n : 𝕜) • eigVec hT hc hInf n,
          eigVec hT hc hInf n⟫_𝕜‖ := by rw [hT']
    _ = ‖(eigSeq hT hc hInf n : 𝕜) * ⟪eigVec hT hc hInf n, eigVec hT hc hInf n⟫_𝕜‖ := by
        rw [inner_smul_left, RCLike.conj_ofReal]
    _ = |eigSeq hT hc hInf n| := by
        rw [inner_self_eq_norm_sq_to_K, hn1]
        simp

/-- The moduli of the eigenvalues are antitone: `λₙ₊₁` lies in the
orthogonal complement used at stage `n`, where `λₙ` is maximal. -/
private theorem abs_eigSeq_antitone {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H) :
    Antitone (fun n => |eigSeq hT hc hInf n|) := by
  apply antitone_nat_of_succ_le
  intro n
  have hmax := (stepProps_eig hT hc hInf n).2.2.2 (eigVec hT hc hInf (n + 1))
      (stepProps_eig hT hc hInf (n + 1)).1 (fun j hj =>
        (stepProps_eig hT hc hInf (n + 1)).2.2.1 j (by omega))
  rw [← rayleigh_at_eigVec hT hc hInf (n + 1)]
  exact hmax

/-- The moduli of the eigenvalues tend to `0`. If they stayed above some
`ε > 0`, the eigenvalues would take some value `μ` infinitely often (only
finitely many eigenvalues lie above `ε`), giving an infinite orthonormal
family inside the finite-dimensional eigenspace for `μ`. -/
private theorem tendsto_abs_eigSeq {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H) :
    Tendsto (fun n => |eigSeq hT hc hInf n|) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hge : ∀ n, ε ≤ |eigSeq hT hc hInf n| := by
    intro n
    obtain ⟨m, hmn, hm⟩ := hcon n
    have hm' : ε ≤ |eigSeq hT hc hInf m| := by
      have h2 := hm
      rw [dist_eq_norm] at h2
      simpa using h2
    exact le_trans hm' (abs_eigSeq_antitone hT hc hInf hmn)
  have hfin := finite_eigenvalues_of_ge hT hc hε
  set f : ℕ → 𝕜 := fun n => (eigSeq hT hc hInf n : 𝕜) with hf
  have hfA : ∀ n, f n ∈ {μ : 𝕜 | Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧
      ε ≤ ‖μ‖} := by
    intro n
    refine ⟨?_, ?_⟩
    · apply Module.End.hasEigenvalue_of_hasEigenvector
      refine ⟨Module.End.mem_eigenspace_iff.mpr (stepProps_eig hT hc hInf n).2.1, ?_⟩
      intro h0
      have hn1 := (stepProps_eig hT hc hInf n).1
      rw [h0, norm_zero] at hn1
      exact zero_ne_one hn1
    · rw [hf, RCLike.norm_ofReal]
      exact hge n
  obtain ⟨μ, hμinf⟩ : ∃ μ, {n | f n = μ}.Infinite := by
    by_contra hnone
    push Not at hnone
    have hcover : (Set.univ : Set ℕ) =
        ⋃ μ ∈ {μ : 𝕜 | Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧ ε ≤ ‖μ‖},
          {n | f n = μ} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact ⟨f x, hfA x, rfl⟩
    have huniv : (Set.univ : Set ℕ).Finite := by
      rw [hcover]
      exact hfin.biUnion (fun μ _ => hnone μ)
    exact Set.Infinite.not_finite Set.infinite_univ huniv
  have hμ0 : μ ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hμinf.nonempty
    have hmem : ε ≤ ‖μ‖ := by
      have h2 := (hfA n).2
      have hn' : f n = μ := hn
      rw [hn'] at h2
      exact h2
    rw [h0, norm_zero] at hmem
    exact not_lt_of_ge hmem hε
  have hfinEig : FiniteDimensional 𝕜
      ↥(Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ0
  have hmem : ∀ i : {n | f n = μ},
      eigVec hT hc hInf i.1 ∈ Module.End.eigenspace (T : H →ₗ[𝕜] H) μ := by
    intro i
    apply Module.End.mem_eigenspace_iff.mpr
    have h1 := (stepProps_eig hT hc hInf i.1).2.1
    have h2 : (eigSeq hT hc hInf i.1 : 𝕜) = μ := i.2
    rw [h2] at h1
    exact h1
  set v : {n | f n = μ} → ↥(Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) :=
    fun i => ⟨eigVec hT hc hInf i.1, hmem i⟩ with hv
  have horth : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Submodule.coe_inner]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K,
        (stepProps_eig hT hc hInf i.1).1]
      simp
    · have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
      rw [ite_eq_right hij]
      have h2 := orthonormal_iff_ite.mp (orthonormal_eigVec hT hc hInf) i.1 j.1
      rw [ite_eq_right hij'] at h2
      exact h2
  have hlin : LinearIndependent 𝕜 v := horth.linearIndependent
  have hfinI : Finite {n | f n = μ} := LinearIndependent.finite hlin
  exact (not_finite_iff_infinite.mpr (Set.infinite_coe_iff.mpr hμinf)) hfinI

/-- **Maximum principle for compact self-adjoint operators.** Let `T` be a
compact self-adjoint operator on an infinite-dimensional Hilbert space.
Then there are real numbers `λₙ` and pairwise orthonormal unit vectors
`uₙ` such that `T uₙ = λₙ • uₙ`, `|λₙ₊₁| ≤ |λₙ|`, `|λₙ| → 0`, and for
each `n`, `|λₙ|` is the maximum of `‖⟪T x, x⟫‖` over unit vectors `x`
orthogonal to `u₀, …, uₙ₋₁`, attained at `uₙ`. -/
theorem exists_ordered_eigenvalue_sequence {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H) :
    ∃ (s : ℕ → ℝ) (u : ℕ → H),
      (∀ n, T (u n) = (s n : 𝕜) • u n) ∧
      Orthonormal 𝕜 u ∧
      (∀ n, |s (n + 1)| ≤ |s n|) ∧
      Tendsto (fun n => |s n|) atTop (𝓝 0) ∧
      ∀ n, (∀ x : H, ‖x‖ = 1 → (∀ j < n, ⟪x, u j⟫_𝕜 = 0) → ‖⟪T x, x⟫_𝕜‖ ≤ |s n|) ∧
        ‖⟪T (u n), u n⟫_𝕜‖ = |s n| := by
  refine ⟨eigSeq hT hc hInf, eigVec hT hc hInf, ?_, orthonormal_eigVec hT hc hInf,
    fun n => abs_eigSeq_antitone hT hc hInf (Nat.le_succ n),
    tendsto_abs_eigSeq hT hc hInf, ?_⟩
  · intro n
    exact (stepProps_eig hT hc hInf n).2.1
  · intro n
    exact ⟨(stepProps_eig hT hc hInf n).2.2.2,
      rayleigh_at_eigVec hT hc hInf n⟩

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple
