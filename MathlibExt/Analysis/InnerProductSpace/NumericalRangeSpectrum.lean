/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorff
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# The spectrum lies in the closure of the (conjugate) numerical range

For a bounded operator `A` on a complex Hilbert space, the spectrum is
controlled by the numerical range `W(A) = { ⟪A x, x⟫ : ‖x‖ = 1 }` defined in
`MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorff`. Because Mathlib's
inner product is conjugate-linear in its first argument, `⟪A x, x⟫` is the
conjugate of the usual convention `⟪x, A x⟫`; the spectrum inclusion therefore
appears in conjugated form: if `λ` is in the spectrum of `A`, then `conj λ` is
in the closure of `W(A)`. The scalar operator `A = I • 1` is the sharp test of
the convention: its spectrum is `{I}` while its numerical range is `{-I}`.

This is a companion to the spectral-theory material of the `v1` Functional
Analysis book (April 2021 section) and to the Toeplitz–Hausdorff theorem on
`numericalRange` in base MathlibExt. The proof is the standard bounded-below
argument: staying away from the closure of the numerical range forces both
`A - conj μ • 1` and its adjoint to be bounded below, hence the operator is
bijective, hence a unit.

## Main declarations

* `isUnit_of_notMem_closure_numericalRange` : if `μ` stays away from the
  closure of `W(A)`, then `A - conj μ • 1` is a unit.
* `conj_mem_closure_numericalRange_of_mem_spectrum` : every spectral value
  `λ` has `conj λ` in the closure of `W(A)`.
* `spectrum_subset_star_image_closure_numericalRange` : the spectrum is
  contained in the conjugate of the closure of `W(A)`.
* `conj_mem_numericalRange_of_exists_unit_eigenvector` : an eigenvalue `λ`
  has `conj λ` in `W(A)` itself, not just in its closure.
* `numericalRange_subset_closedBall_norm` : `W(A)` lies in the closed ball
  of radius `‖A‖`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.NumericalRangeSpectrum

open scoped _root_.InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- If the inner products `⟪T u, u⟫` are bounded below by `δ` on unit vectors,
then `T` is bounded below by the same constant. -/
private theorem le_norm_of_unit_inner_norm_ge {T : E →L[ℂ] E} {δ : ℝ}
    (h : ∀ u : E, ‖u‖ = 1 → δ ≤ ‖inner (𝕜 := ℂ) (T u) u‖) (x : E) :
    δ * ‖x‖ ≤ ‖T x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set c : ℝ := ‖x‖ with hc
    set u : E := ((c : ℂ))⁻¹ • x with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hxn.le, inv_mul_cancel₀ hxn.ne']
    have hxu : x = (c : ℂ) • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxn.ne'), one_smul]
    have hinner : inner (𝕜 := ℂ) (T x) x = (c : ℂ) ^ 2 * inner (𝕜 := ℂ) (T u) u := by
      conv_lhs => rw [hxu]
      rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      ring
    have h1 := h u hu1
    have h2 : ‖inner (𝕜 := ℂ) (T x) x‖ ≤ ‖T x‖ * c := norm_inner_le_norm _ _
    have hnorm : ‖(c : ℂ)‖ = c := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxn.le]
    have h3 : ‖inner (𝕜 := ℂ) (T x) x‖ = c ^ 2 * ‖inner (𝕜 := ℂ) (T u) u‖ := by
      rw [hinner, norm_mul, norm_pow, hnorm]
    have h4 : c ^ 2 * δ ≤ ‖T x‖ * c := by
      calc c ^ 2 * δ ≤ c ^ 2 * ‖inner (𝕜 := ℂ) (T u) u‖ :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
        _ = ‖inner (𝕜 := ℂ) (T x) x‖ := h3.symm
        _ ≤ ‖T x‖ * c := h2
    have h5 : c * (c * δ) ≤ c * ‖T x‖ := by
      calc c * (c * δ) = c ^ 2 * δ := by ring
        _ ≤ ‖T x‖ * c := h4
        _ = c * ‖T x‖ := by ring
    have h6 : c * δ ≤ ‖T x‖ := le_of_mul_le_mul_left h5 hxn
    rw [mul_comm]
    exact h6

/-- If `μ` is at distance at least `δ` from every point of the numerical range
of `A`, then `⟪(A - conj μ • 1) u, u⟫` has norm at least `δ` on unit vectors:
indeed it equals `⟪A u, u⟫ - μ`. -/
private theorem inner_norm_ge_of_notMem_closure {A : E →L[ℂ] E} {μ : ℂ} {δ : ℝ}
    (hdist : ∀ c ∈ ToeplitzHausdorffWanted.numericalRange A, δ ≤ dist μ c)
    {u : E} (hu : ‖u‖ = 1) :
    δ ≤ ‖inner (𝕜 := ℂ) ((A - (starRingEnd ℂ) μ • (1 : E →L[ℂ] E)) u) u‖ := by
  have hDeq : inner (𝕜 := ℂ) ((A - (starRingEnd ℂ) μ • (1 : E →L[ℂ] E)) u) u
      = inner (𝕜 := ℂ) (A u) u - μ := by
    rw [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
      inner_self_eq_norm_sq_to_K, hu, starRingEnd_self_apply]
    simp
  rw [hDeq]
  have hmem : inner (𝕜 := ℂ) (A u) u
      ∈ ToeplitzHausdorffWanted.numericalRange A :=
    ToeplitzHausdorffWanted.inner_mem_numericalRange A hu
  have hle := hdist _ hmem
  rwa [dist_eq_norm, norm_sub_rev] at hle

/-- The adjoint inherits the unit-vector inner-product lower bound, since
`⟪T† u, u⟫ = conj ⟪T u, u⟫` has the same norm. -/
private theorem inner_norm_ge_of_adjoint [CompleteSpace E] {T : E →L[ℂ] E} {δ : ℝ}
    (h : ∀ u : E, ‖u‖ = 1 → δ ≤ ‖inner (𝕜 := ℂ) (T u) u‖) {u : E} (hu : ‖u‖ = 1) :
    δ ≤ ‖inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint T) u) u‖ := by
  have h2 : inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint T) u) u
      = (starRingEnd ℂ) (inner (𝕜 := ℂ) (T u) u) := by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
  rw [h2, Complex.norm_conj]
  exact h u hu

/-- If `μ` stays away from the closure of the numerical range of `A`, then
`A - conj μ • 1` is a unit: it and its adjoint are bounded below, so it is
injective with closed range, and its range has trivial orthogonal complement,
hence it is surjective. -/
theorem isUnit_of_notMem_closure_numericalRange [CompleteSpace E] {A : E →L[ℂ] E}
    {μ : ℂ} (hμ : μ ∉ closure (ToeplitzHausdorffWanted.numericalRange A)) :
    IsUnit (A - (starRingEnd ℂ) μ • (1 : E →L[ℂ] E)) := by
  rw [Metric.mem_closure_iff] at hμ
  push Not at hμ
  obtain ⟨δ, hδ, hdist⟩ := hμ
  set D : E →L[ℂ] E := A - (starRingEnd ℂ) μ • (1 : E →L[ℂ] E) with hDdef
  have hD : ∀ x : E, δ * ‖x‖ ≤ ‖D x‖ :=
    fun x => le_norm_of_unit_inner_norm_ge
      (fun u hu => inner_norm_ge_of_notMem_closure hdist hu) x
  have hDadj : ∀ x : E, δ * ‖x‖ ≤ ‖(ContinuousLinearMap.adjoint D) x‖ :=
    fun x => le_norm_of_unit_inner_norm_ge
      (fun u hu => inner_norm_ge_of_adjoint
        (fun v hv => inner_norm_ge_of_notMem_closure hdist hv) hu) x
  have hinj : Function.Injective D := by
    intro x y hxy
    have h0 : D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hle := hD (x - y)
    rw [h0, norm_zero] at hle
    have hnorm : ‖x - y‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hpos' : 0 < δ * ‖x - y‖ := mul_pos hδ hpos
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hinjAdj : Function.Injective (ContinuousLinearMap.adjoint D) := by
    intro x y hxy
    have h0 : (ContinuousLinearMap.adjoint D) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hle := hDadj (x - y)
    rw [h0, norm_zero] at hle
    have hnorm : ‖x - y‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hpos' : 0 < δ * ‖x - y‖ := mul_pos hδ hpos
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hanti : AntilipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ D :=
    AntilipschitzWith.of_le_mul_dist fun x y => by
      show dist x y ≤ δ⁻¹ * dist (D x) (D y)
      rw [dist_eq_norm, dist_eq_norm]
      have hle := hD (x - y)
      rw [map_sub] at hle
      calc ‖x - y‖ = δ⁻¹ * (δ * ‖x - y‖) := by
            rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
        _ ≤ δ⁻¹ * ‖D x - D y‖ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hδ.le)
  have hclosed : IsClosed (↑D.range : Set E) :=
    hanti.isClosed_range D.uniformContinuous
  have horth : D.rangeᗮ = ⊥ := by
    rw [D.orthogonal_range]
    exact LinearMap.ker_eq_bot.mpr hinjAdj
  have hcl : D.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth]
    exact Submodule.bot_orthogonal_eq_top
  have hrange : D.range = ⊤ := by
    rw [← hclosed.submodule_topologicalClosure_eq]
    exact hcl
  have hsurj : Function.Surjective D := by
    show Function.Surjective ⇑(D : E →ₗ[ℂ] E)
    rw [← LinearMap.range_eq_top]
    exact hrange
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, hsurj⟩

/-- Every spectral value `z` of `A` has `conj z` in the closure of the
numerical range of `A`. -/
theorem conj_mem_closure_numericalRange_of_mem_spectrum [CompleteSpace E]
    {A : E →L[ℂ] E} {z : ℂ} (hz : z ∈ spectrum ℂ A) :
    (starRingEnd ℂ) z ∈ closure (ToeplitzHausdorffWanted.numericalRange A) := by
  by_contra h
  have hun : IsUnit (A - (starRingEnd ℂ) ((starRingEnd ℂ) z) • (1 : E →L[ℂ] E)) :=
    isUnit_of_notMem_closure_numericalRange h
  rw [starRingEnd_self_apply] at hun
  rw [spectrum.mem_iff] at hz
  apply hz
  rw [Algebra.algebraMap_eq_smul_one]
  simpa [neg_sub] using hun.neg

/-- The spectrum of `A` is contained in the conjugate of the closure of its
numerical range. -/
theorem spectrum_subset_star_image_closure_numericalRange [CompleteSpace E]
    (A : E →L[ℂ] E) :
    spectrum ℂ A ⊆ (starRingEnd ℂ) '' closure (ToeplitzHausdorffWanted.numericalRange A) := by
  intro z hz
  have h := conj_mem_closure_numericalRange_of_mem_spectrum hz
  exact ⟨(starRingEnd ℂ) z, h, by simp⟩

/-- An eigenvalue `z` of `A` has `conj z` in the numerical range itself, not
just in its closure: for a unit eigenvector `x`, `⟪A x, x⟫ = conj z`. -/
theorem conj_mem_numericalRange_of_exists_unit_eigenvector {A : E →L[ℂ] E} {z : ℂ}
    (h : ∃ x : E, ‖x‖ = 1 ∧ A x = z • x) :
    (starRingEnd ℂ) z ∈ ToeplitzHausdorffWanted.numericalRange A := by
  obtain ⟨x, hx, hAx⟩ := h
  refine ⟨x, hx, ?_⟩
  rw [hAx, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
  simp

/-- The numerical range of `A` lies in the closed ball of radius `‖A‖`. -/
theorem numericalRange_subset_closedBall_norm (A : E →L[ℂ] E) :
    ToeplitzHausdorffWanted.numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro c hc
  obtain ⟨x, hx, hxc⟩ := hc
  rw [← hxc, Metric.mem_closedBall, dist_zero_right]
  calc ‖inner (𝕜 := ℂ) (A x) x‖ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ := by rw [hx]; simp

end MathlibExt.Analysis.InnerProductSpace.NumericalRangeSpectrum
