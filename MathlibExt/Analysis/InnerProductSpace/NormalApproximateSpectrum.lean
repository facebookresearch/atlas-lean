/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Approximate point spectrum of normal operators

For a bounded operator `T` on a Hilbert space, `μ` is an **approximate
eigenvalue** if there are unit vectors `xₙ` with `(μ • 1 - T) xₙ → 0`. The
main result is that for a **normal** operator, the spectrum is exactly the
approximate point spectrum: every spectral value admits approximate
eigenvectors. In particular the residual spectrum of a normal operator is
empty: a normal operator with trivial kernel has dense range.

The proof of the forward direction is the usual bounded-below dichotomy.
If `S = μ • 1 - T` is not bounded below, unit vectors with arbitrarily small
residual exist directly. If `S` is bounded below, then `S` is a closed
embedding, hence injective with closed range; normality gives
`S.rangeᗮ = S.ker = ⊥`, so the range is everything, and `S` is a unit,
contradicting `μ ∈ spectrum 𝕜 T`. The converse needs no normality: a unit
`μ • 1 - T` would send the approximate eigenvectors to vectors whose norms
are squeezed to `0`, contradicting `‖xₙ‖ = 1`.

For self-adjoint operators this is Weyl's criterion. The statement is
companion material to the v1 spectral-theory section
(`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`), which
proves the Fredholm alternative for compact self-adjoint operators but does
not state the approximate-spectrum characterization; it is not one of the
72 v1 targets.

Main results:

* `IsApproximateEigenvalue`: `μ` is an approximate eigenvalue of `T`.
* `isApproximateEigenvalue_iff_forall_eps`: the `∀ ε > 0` characterization.
* `isApproximateEigenvalue_of_mem_spectrum`: for normal `T`, every spectral
  value is an approximate eigenvalue.
* `mem_spectrum_of_isApproximateEigenvalue`: every approximate eigenvalue
  (of any `T`) is a spectral value.
* `mem_spectrum_iff_isApproximateEigenvalue`: the two directions combined,
  for normal `T`, plus the self-adjoint specialization.
* `isApproximateEigenvalue_of_hasEigenvalue`: exact eigenvalues are
  approximate eigenvalues.
* `denseRange_of_isStarNormal_of_ker_eq_bot`: a normal operator with
  trivial kernel has dense range.
-/

@[expose] public section

open Function Set Filter Topology

namespace MathlibExt.Analysis.InnerProductSpace.NormalApproximateSpectrum

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- `μ` is an **approximate eigenvalue** of `T` if there is a sequence of
unit vectors `xₙ` with `(μ • 1 - T) xₙ → 0`. -/
def IsApproximateEigenvalue (T : E →L[𝕜] E) (μ : 𝕜) : Prop :=
  ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
    Tendsto (fun n => (μ • (1 : E →L[𝕜] E) - T) (x n)) atTop (𝓝 0)

omit [CompleteSpace E] in
/-- The `∀ ε > 0` characterization of approximate eigenvalues. -/
theorem isApproximateEigenvalue_iff_forall_eps (T : E →L[𝕜] E) (μ : 𝕜) :
    IsApproximateEigenvalue T μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖x‖ = 1 ∧
        ‖(μ • (1 : E →L[𝕜] E) - T) x‖ < ε := by
  constructor
  · rintro ⟨x, hxnorm, hxlim⟩ ε hε
    have h := (tendsto_zero_iff_norm_tendsto_zero.mp hxlim).eventually
      (eventually_lt_nhds hε)
    obtain ⟨n, hn⟩ := h.exists
    exact ⟨x n, hxnorm n, hn⟩
  · intro h
    have hchoice : ∀ n : ℕ, ∃ x : E, ‖x‖ = 1 ∧
        ‖(μ • (1 : E →L[𝕜] E) - T) x‖ < 1 / (n + 1 : ℝ) :=
      fun n => h _ (by positivity)
    choose x hxnorm hxbound using hchoice
    refine ⟨x, hxnorm, ?_⟩
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hle : ∀ n : ℕ, 0 ≤ ‖(μ • (1 : E →L[𝕜] E) - T) (x n)‖ ∧
        ‖(μ • (1 : E →L[𝕜] E) - T) (x n)‖ ≤ 1 / (n + 1 : ℝ) :=
      fun n => ⟨norm_nonneg _, (hxbound n).le⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => (hle n).1) (fun n => (hle n).2)

/-- Shifting by a scalar preserves normality. -/
theorem isStarNormal_smul_one_sub (T : E →L[𝕜] E) (hT : IsStarNormal T) (μ : 𝕜) :
    IsStarNormal (μ • (1 : E →L[𝕜] E) - T) := by
  rw [isStarNormal_iff]
  show Commute (star (μ • (1 : E →L[𝕜] E) - T)) _
  rw [star_sub, star_smul, star_one]
  apply Commute.sub_left
  · exact (Commute.one_left _).smul_left _
  · apply Commute.sub_right
    · exact (Commute.one_right _).smul_right _
    · exact (isStarNormal_iff T).mp hT

/-- Every spectral value of a normal operator is an approximate eigenvalue. -/
theorem isApproximateEigenvalue_of_mem_spectrum {T : E →L[𝕜] E} (hT : IsStarNormal T)
    {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 T) : IsApproximateEigenvalue T μ := by
  rw [isApproximateEigenvalue_iff_forall_eps]
  intro ε hε
  set S := μ • (1 : E →L[𝕜] E) - T with hS
  have hSnormal : IsStarNormal S := isStarNormal_smul_one_sub T hT μ
  have hSnotunit : ¬ IsUnit S := by
    rw [hS]
    have h := spectrum.mem_iff.mp hμ
    rwa [Algebra.algebraMap_eq_smul_one] at h
  by_cases hbb : ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ≤ ‖S x‖
  · -- `S` bounded below: then `S` is a unit, contradicting `μ ∈ spectrum 𝕜 T`.
    obtain ⟨c, hc, hcb⟩ := hbb
    obtain ⟨K, hK⟩ := antilipschitzWith_iff_exists_mul_le_norm.mpr ⟨c, hc, hcb⟩
    have hclosed : IsClosedEmbedding (S : E → E) :=
      hK.isClosedEmbedding S.uniformContinuous
    have hinj : Function.Injective (S : E → E) := hclosed.isEmbedding.injective
    have hker : (S : E →L[𝕜] E).ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    have hrange_closed : IsClosed (LinearMap.range (S : E →L[𝕜] E).toLinearMap : Set E) := by
      rw [LinearMap.coe_range]
      exact hclosed.isClosed_range
    have hcomp : CompleteSpace (LinearMap.range (S : E →L[𝕜] E).toLinearMap) :=
      hrange_closed.completeSpace_coe
    have hort : (LinearMap.range (S : E →L[𝕜] E).toLinearMap)ᗮ = ⊥ := by
      rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hSnormal, hker]
    have hrange_top : LinearMap.range (S : E →L[𝕜] E).toLinearMap = ⊤ :=
      Submodule.orthogonal_eq_bot_iff.mp hort
    have hsurj : Function.Surjective (S : E → E) :=
      (LinearMap.range_eq_top (f := (S : E →L[𝕜] E).toLinearMap)).mp hrange_top
    exact absurd (ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩) hSnotunit
  · -- `S` not bounded below: a unit vector with residual `< ε` exists directly.
    push Not at hbb
    obtain ⟨x, hx⟩ := hbb ε hε
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero, norm_zero, mul_zero] at hx
      exact lt_irrefl _ hx
    have hcnorm : ‖((‖x‖ : 𝕜))⁻¹‖ = ‖x‖⁻¹ := by
      rw [norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    refine ⟨((‖x‖ : 𝕜))⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul, hcnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
    · calc ‖S (((‖x‖ : 𝕜))⁻¹ • x)‖ = ‖x‖⁻¹ * ‖S x‖ := by
            rw [map_smul, norm_smul, hcnorm]
        _ < ‖x‖⁻¹ * (ε * ‖x‖) :=
            mul_lt_mul_of_pos_left hx (inv_pos.mpr (norm_pos_iff.mpr hx0))
        _ = ε * (‖x‖⁻¹ * ‖x‖) := by ring
        _ = ε := by
            rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0), mul_one]

omit [CompleteSpace E] in
/-- Every approximate eigenvalue is a spectral value (no normality needed). -/
theorem mem_spectrum_of_isApproximateEigenvalue {T : E →L[𝕜] E} {μ : 𝕜}
    (h : IsApproximateEigenvalue T μ) : μ ∈ spectrum 𝕜 T := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  intro hunit
  obtain ⟨x, hxnorm, hxlim⟩ := h
  obtain ⟨u, hu⟩ := hunit
  have hrec : ∀ n : ℕ, x n =
      (↑u⁻¹ : E →L[𝕜] E) ((μ • (1 : E →L[𝕜] E) - T) (x n)) := by
    intro n
    have h1 : (↑u⁻¹ : E →L[𝕜] E) ((↑u : E →L[𝕜] E) (x n)) = x n := by
      show ((↑u⁻¹ : E →L[𝕜] E) * (↑u : E →L[𝕜] E)) (x n) = x n
      rw [Units.inv_mul]
      simp
    rw [← hu]
    exact h1.symm
  have hbound : ∀ n : ℕ, ‖x n‖ ≤
      ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖(μ • (1 : E →L[𝕜] E) - T) (x n)‖ := by
    intro n
    nth_rewrite 1 [hrec n]
    exact (↑u⁻¹ : E →L[𝕜] E).le_opNorm _
  have hlim0 : Tendsto (fun n : ℕ => ‖x n‖) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ =>
        ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖(μ • (1 : E →L[𝕜] E) - T) (x n)‖) atTop
        (𝓝 (‖(↑u⁻¹ : E →L[𝕜] E)‖ * 0)) :=
      tendsto_const_nhds.mul (tendsto_zero_iff_norm_tendsto_zero.mp hxlim)
    rw [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun n => norm_nonneg _) (hbound)
  have h10 : (1 : ℝ) = 0 := by
    simp only [hxnorm] at hlim0
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    exact tendsto_nhds_unique h1 hlim0
  exact one_ne_zero h10

/-- For a normal operator, the spectrum is exactly the approximate point
spectrum. -/
theorem mem_spectrum_iff_isApproximateEigenvalue {T : E →L[𝕜] E} (hT : IsStarNormal T)
    {μ : 𝕜} : μ ∈ spectrum 𝕜 T ↔ IsApproximateEigenvalue T μ :=
  ⟨isApproximateEigenvalue_of_mem_spectrum hT,
    mem_spectrum_of_isApproximateEigenvalue⟩

/-- Weyl's criterion: for a self-adjoint operator, the spectrum is exactly
the approximate point spectrum. -/
theorem mem_spectrum_iff_isApproximateEigenvalue_of_isSelfAdjoint {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) {μ : 𝕜} :
    μ ∈ spectrum 𝕜 T ↔ IsApproximateEigenvalue T μ :=
  mem_spectrum_iff_isApproximateEigenvalue hT.isStarNormal

omit [CompleteSpace E] in
/-- Exact eigenvalues are approximate eigenvalues. -/
theorem isApproximateEigenvalue_of_hasEigenvalue {T : E →L[𝕜] E} {μ : 𝕜}
    (h : Module.End.HasEigenvalue (T.toLinearMap) μ) : IsApproximateEigenvalue T μ := by
  rw [Module.End.hasEigenvalue_iff] at h
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h
  have hxeig : T x = μ • x :=
    (Module.End.mem_eigenspace_iff (f := T.toLinearMap)).mp hx
  have hcnorm : ‖((‖x‖ : 𝕜))⁻¹‖ = ‖x‖⁻¹ := by
    rw [norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  refine ⟨fun _ => ((‖x‖ : 𝕜))⁻¹ • x, fun _ => ?_, ?_⟩
  · rw [norm_smul, hcnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  · have hzero : ∀ n : ℕ,
        (μ • (1 : E →L[𝕜] E) - T) (((‖x‖ : 𝕜))⁻¹ • x) = 0 := by
      intro n
      rw [map_smul]
      have hres : (μ • (1 : E →L[𝕜] E) - T) x = 0 := by
        rw [sub_apply, smul_apply, hxeig]
        simp
      rw [hres, smul_zero]
    have hfun : (fun n : ℕ =>
        (μ • (1 : E →L[𝕜] E) - T) (((‖x‖ : 𝕜))⁻¹ • x)) = fun _ => (0 : E) :=
      funext fun n => hzero n
    rw [hfun]
    exact tendsto_const_nhds

/-- A normal operator with trivial kernel has dense range: the residual
spectrum of a normal operator is empty. -/
theorem denseRange_of_isStarNormal_of_ker_eq_bot {T : E →L[𝕜] E} (hT : IsStarNormal T)
    (hker : T.ker = ⊥) : DenseRange (T : E → E) := by
  have hort : T.rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hT, hker]
  have hcl : T.range.topologicalClosure = ⊤ := by
    have hcomp : CompleteSpace (T.range.topologicalClosure) :=
      (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    have hort2 : T.range.topologicalClosureᗮ = ⊥ := by
      rw [Submodule.orthogonal_closure, hort]
    exact Submodule.orthogonal_eq_bot_iff.mp hort2
  have hdense : Dense (T.range : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hcl
  rwa [LinearMap.coe_range] at hdense

end MathlibExt.Analysis.InnerProductSpace.NormalApproximateSpectrum
