/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Riesz–Schauder kernel and range results

Source context: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.fredholm_alternative_full` (May 11, 2021), the archived
self-adjoint Hilbert-space Fredholm alternative. This module generalizes its
kernel and closed-range conclusions to general compact operators on Banach
spaces over `RCLike` scalars, at nonzero `μ`.

The kernel proof makes the identity on the kernel compact. The range proof
uses a Hahn–Banach projection and compactness on a complement to obtain a
lower bound. The alternative then uses Mathlib's compact-operator
eigenvalue/resolvent dichotomy. The archived self-adjoint proof is not imported.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauder

open Filter Topology

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]
variable {T : E →L[𝕜] E} {μ : 𝕜}

/-- **Riesz–Schauder theorem, kernel part.** For a compact operator `T` on a Banach
space and `μ ≠ 0`, the kernel of `μ • 1 - T` is finite-dimensional. The proof
is the standard restriction trick: `T` preserves the kernel, and there it agrees
with `μ • 1`, so the identity on the kernel is compact. -/
theorem finiteDimensional_ker (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (LinearMap.ker ((μ • 1 - T : E →L[𝕜] E).toLinearMap)) := by
  classical
  have hpres : ∀ v ∈ LinearMap.ker ((μ • 1 - T : E →L[𝕜] E).toLinearMap), T v ∈
      LinearMap.ker ((μ • 1 - T : E →L[𝕜] E).toLinearMap) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hcomm : ((μ • 1 - T : E →L[𝕜] E).toLinearMap) (T v)
        = T (((μ • 1 - T : E →L[𝕜] E).toLinearMap) v) := by
      simp [map_sub, map_smul]
    rw [hcomm, hv, map_zero]
  have hKcomplete : CompleteSpace
      (LinearMap.ker ((μ • 1 - T : E →L[𝕜] E).toLinearMap)) :=
    completeSpace_coe_iff_isComplete.mpr (μ • 1 - T : E →L[𝕜] E).isClosed_ker.isComplete
  have hcomp : IsCompactOperator
      (T.toLinearMap.restrict hpres) := hT.restrict' hpres
  have hrestrict : T.toLinearMap.restrict hpres
      = μ • (1 : Module.End 𝕜
        (LinearMap.ker ((μ • 1 - T : E →L[𝕜] E).toLinearMap))) := by
    apply LinearMap.ext
    rintro ⟨v, hv⟩
    apply Subtype.ext
    have h0 : ((μ • 1 - T : E →L[𝕜] E)) v = 0 := LinearMap.mem_ker.mp hv
    simp only [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] at h0
    show T v = μ • v
    exact h0.symm
  rw [hrestrict] at hcomp
  simp only [LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hcomp
  exact FiniteDimensional.of_isCompactOperator_id hcomp

omit [CompleteSpace E] in
/-- A finite-dimensional subspace of a normed space is topologically complemented:
there is a continuous projection onto it. The projection is built from a basis,
with the coordinate functionals extended to the whole space by Hahn–Banach. -/
theorem exists_continuous_projection (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] :
    ∃ P : E →L[𝕜] E, (∀ x ∈ K, P x = x) ∧ ∀ x, P x ∈ K := by
  classical
  let b := Module.finBasis 𝕜 K
  have hcoord : ∀ i, ∃ g : E →L[𝕜] 𝕜, ∀ x : K, g x = b.coord i x := by
    intro i
    obtain ⟨g, hg, -⟩ := exists_extension_norm_eq K
      (⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩ : StrongDual 𝕜 K)
    exact ⟨g, hg⟩
  choose g hg using hcoord
  refine ⟨∑ i, (g i).smulRight ((b i : K) : E), ?_, ?_⟩
  · intro x hx
    have hgi : ∀ i, g i x = b.coord i ⟨x, hx⟩ := fun i ↦ hg i ⟨x, hx⟩
    have hsum : (∑ i, b.coord i ⟨x, hx⟩ • ((b i : K) : E)) = x := by
      simp only [Module.Basis.coord_apply, ← Submodule.coe_smul, ← Submodule.coe_sum,
        b.sum_repr]
    calc (∑ i, (g i).smulRight ((b i : K) : E)) x
        = ∑ i, b.coord i ⟨x, hx⟩ • ((b i : K) : E) := by
          simp [sum_apply, ContinuousLinearMap.smulRight_apply, hgi]
      _ = x := hsum
  · intro x
    rw [sum_apply]
    apply Submodule.sum_mem
    intro i _
    rw [ContinuousLinearMap.smulRight_apply]
    exact Submodule.smul_mem K _ (b i).2

/-- **Riesz–Schauder theorem, range part.** For a compact operator `T` on a Banach
space and `μ ≠ 0`, the range of `μ • 1 - T` is closed. The proof restricts
`μ • 1 - T` to a closed complement of its kernel, where it is bounded below:
a sequence argument using compactness of `T` shows the restriction is
antilipschitz, hence its range is closed. -/
theorem isClosed_range_smul_one_sub (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    IsClosed (LinearMap.range ((μ • 1 - T : E →L[𝕜] E).toLinearMap) : Set E) := by
  classical
  set S : E →L[𝕜] E := μ • 1 - T with hS
  set K := LinearMap.ker S.toLinearMap with hK
  have hKfin : FiniteDimensional 𝕜 K := finiteDimensional_ker hT hμ
  obtain ⟨P, hPid, hPmem⟩ := exists_continuous_projection K
  set C := LinearMap.ker P.toLinearMap with hC
  have hCclosed : IsClosed (C : Set E) := P.isClosed_ker
  have : CompleteSpace C := completeSpace_coe_iff_isComplete.mpr hCclosed.isComplete
  set SC : C →L[𝕜] E := S.comp C.subtypeL with hSC
  have hrange : LinearMap.range S.toLinearMap = LinearMap.range SC.toLinearMap := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      refine ⟨⟨x - P x, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker]
        simp [map_sub, hPid (P x) (hPmem x)]
      · show S (x - P x) = S x
        rw [map_sub]
        have hPx : S (P x) = 0 := LinearMap.mem_ker.mp (hPmem x)
        rw [hPx, sub_zero]
    · rintro y ⟨⟨x, _⟩, rfl⟩
      exact ⟨x, rfl⟩
  have hanti : ∃ c > 0, ∀ x : C, c * ‖x‖ ≤ ‖SC x‖ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ n : ℕ, ∃ y : C, ‖y‖ = 1 ∧ ‖SC y‖ < (n + 1 : ℝ)⁻¹ := by
      intro n
      obtain ⟨x, hx⟩ := hcon ((n + 1 : ℝ)⁻¹) (by positivity)
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      have hpos : (0 : ℝ) < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnx)
      refine ⟨(‖x‖⁻¹ : 𝕜) • x, ?_, ?_⟩
      · rw [norm_smul, norm_inv, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnx]
      · rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
        calc ‖x‖⁻¹ * ‖SC x‖ < ‖x‖⁻¹ * ((n + 1 : ℝ)⁻¹ * ‖x‖) := by
              exact mul_lt_mul_of_pos_left hx (inv_pos.mpr hpos)
          _ = (n + 1 : ℝ)⁻¹ := by
              field_simp
    choose y hy_norm hy_bound using hseq
    obtain ⟨Kset, hKcompact, hKsub⟩ := hT.image_closedBall_subset_compact 1
    have hmem : ∀ n, T ((y n : C) : E) ∈ Kset := fun n ↦
      hKsub ⟨(y n : C), by
        have h1 : ‖((y n : C) : E)‖ = 1 := hy_norm n
        simp [Metric.mem_closedBall, dist_eq_norm, h1], rfl⟩
    obtain ⟨w0, -, ψ, hψ, hψlim⟩ := hKcompact.tendsto_subseq hmem
    have hSlim : Tendsto (fun n ↦ S ((y n : C) : E)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) (fun n ↦ ?_) ?_
      · have h := hy_bound n
        rw [hSC, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h
        exact h.le
      · simpa [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hdecomp : ∀ n, ((y n : C) : E)
        = μ⁻¹ • (T ((y n : C) : E) + S ((y n : C) : E)) := by
      intro n
      have h1 : μ • ((y n : C) : E)
          = T ((y n : C) : E) + S ((y n : C) : E) := by
        simp [hS]
      calc ((y n : C) : E) = μ⁻¹ • (μ • ((y n : C) : E)) := by
            rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hμ, one_smul]
        _ = μ⁻¹ • (T ((y n : C) : E) + S ((y n : C) : E)) := by rw [h1]
    have hylim : Tendsto (fun n ↦ ((y (ψ n) : C) : E)) atTop (𝓝 (μ⁻¹ • w0)) := by
      have hTS : Tendsto (fun n ↦ T ((y (ψ n) : C) : E) + S ((y (ψ n) : C) : E))
          atTop (𝓝 (w0 + 0)) :=
        hψlim.add (hSlim.comp hψ.tendsto_atTop)
      have hsmul := hTS.const_smul μ⁻¹
      rw [add_zero] at hsmul
      exact Tendsto.congr (fun n ↦ (hdecomp (ψ n)).symm) hsmul
    set w := μ⁻¹ • w0 with hw
    have hw_norm : ‖w‖ = 1 := by
      have h1 : Tendsto (fun n ↦ ‖((y (ψ n) : C) : E)‖) atTop (𝓝 ‖w‖) := hylim.norm
      have h2 : (fun n ↦ ‖((y (ψ n) : C) : E)‖) = fun _ ↦ (1 : ℝ) := by
        funext n
        exact hy_norm (ψ n)
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hw_C : w ∈ C := hCclosed.mem_of_tendsto hylim (by
      filter_upwards with n
      exact (y (ψ n)).2)
    have hw_S : S w = 0 := by
      have h1 : Tendsto (fun n ↦ S ((y (ψ n) : C) : E)) atTop (𝓝 (S w)) :=
        (S.continuous.tendsto w).comp hylim
      have h2 : Tendsto (fun n ↦ S ((y (ψ n) : C) : E)) atTop (𝓝 0) :=
        hSlim.comp hψ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have hw_K : w ∈ K := LinearMap.mem_ker.mpr hw_S
    have h1 : P w = w := hPid w hw_K
    have h2 : P w = 0 := LinearMap.mem_ker.mp hw_C
    rw [h1] at h2
    rw [h2] at hw_norm
    simp at hw_norm
  obtain ⟨c, hc0, hc⟩ := hanti
  obtain ⟨K', hK'⟩ := antilipschitzWith_iff_exists_mul_le_norm.mpr ⟨c, hc0, hc⟩
  rw [hrange, LinearMap.coe_range]
  exact hK'.isClosed_range SC.uniformContinuous

/-- **Fredholm alternative, Riesz–Schauder form.** For a compact operator `T` on a
Banach space and `μ ≠ 0`, either `μ • 1 - T` is bijective, or its kernel is
nontrivial and finite-dimensional and its range is closed. The bijective case
is Mathlib's Fredholm alternative; the kernel and range statements are the two
lemmas above. -/
theorem fredholm_alternative (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    Function.Bijective (μ • 1 - T : E →L[𝕜] E) ∨
      (LinearMap.ker ((μ • 1 - T : E →L[𝕜] E).toLinearMap) ≠ ⊥ ∧
        FiniteDimensional 𝕜 (LinearMap.ker ((μ • 1 - T : E →L[𝕜] E).toLinearMap)) ∧
        IsClosed (LinearMap.range ((μ • 1 - T : E →L[𝕜] E).toLinearMap) : Set E)) := by
  rcases hT.hasEigenvalue_or_mem_resolventSet hμ with h | h
  · right
    refine ⟨?_, finiteDimensional_ker hT hμ, isClosed_range_smul_one_sub hT hμ⟩
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    rw [ne_eq, Submodule.eq_bot_iff]
    push Not
    exact ⟨v, by
      rw [LinearMap.mem_ker]
      simp [hv.apply_eq_smul], hv.2⟩
  · left
    have hunit : IsUnit (μ • 1 - T : E →L[𝕜] E) := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact spectrum.mem_resolventSet_iff.mp h
    exact ContinuousLinearMap.isUnit_iff_bijective.mp hunit

end

end MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauder
