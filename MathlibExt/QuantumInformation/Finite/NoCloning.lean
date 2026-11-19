/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Two-state no-cloning obstruction

This module proves the two-state pure-state no-cloning obstruction: in a complex
inner-product space, non-orthogonal non-identical unit vectors cannot both be exactly
cloned by a single complex linear isometry `H ⊗ H ≃ₗᵢ H ⊗ H` with a fixed blank state.

## Main results

* `MathlibExt.QuantumInformation.Finite.NoCloning.no_cloning_two_state` – no isometry
  clones two unit states with `0 < ‖⟪ψ, φ⟫‖ < 1` simultaneously.
* `MathlibExt.QuantumInformation.Finite.NoCloning.no_cloning_linear` – if `H` contains two
  orthonormal vectors, no linear map `H ⊗ H → H ⊗ H` (unitary or not) clones every unit vector.

## Source

W. K. Wootters and W. H. Zurek, "A single quantum cannot be cloned",
Nature 299 (1982), 802-803, DOI 10.1038/299802a0.

## Proof note

A cloning isometry preserves inner products, so with `z = ⟪ψ, φ⟫` the tensor
inner-product formula (`TensorProduct.inner_tmul`) and the unit blank state
(`⟪b, b⟫ = 1`) give `z * z = z`, hence `z = 0` or `z = 1`, contradicting
`0 < ‖z‖ < 1`. The unit hypotheses on `ψ` and `φ` are logically redundant in this
formulation but are kept in the public statement for source fidelity.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open TensorProduct

namespace MathlibExt.QuantumInformation.Finite.NoCloning

/-- Two-state pure-state no-cloning obstruction: in a complex inner-product space,
non-orthogonal non-identical unit vectors cannot both be exactly cloned by a single
complex linear isometry `H ⊗ H ≃ₗᵢ H ⊗ H` with a fixed blank state.
Source: W. K. Wootters and W. H. Zurek, "A single quantum cannot be cloned",
Nature 299 (1982), 802-803, DOI 10.1038/299802a0. -/
public theorem no_cloning_two_state
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ φ b : H) (_hψ : ‖ψ‖ = 1) (_hφ : ‖φ‖ = 1) (hb : ‖b‖ = 1)
    (hpos : 0 < ‖⟪ψ, φ⟫_ℂ‖) (hlt : ‖⟪ψ, φ⟫_ℂ‖ < 1) :
    ¬ ∃ (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H)),
      U (ψ ⊗ₜ[ℂ] b) = ψ ⊗ₜ[ℂ] ψ ∧ U (φ ⊗ₜ[ℂ] b) = φ ⊗ₜ[ℂ] φ := by
  rintro ⟨U, hUψ, hUφ⟩
  have hinner : ⟪ψ ⊗ₜ[ℂ] ψ, φ ⊗ₜ[ℂ] φ⟫_ℂ
      = ⟪ψ ⊗ₜ[ℂ] b, φ ⊗ₜ[ℂ] b⟫_ℂ := by
    rw [← hUψ, ← hUφ, LinearIsometryEquiv.inner_map_map]
  rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul] at hinner
  have hbb : ⟪b, b⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hb]
    norm_num
  rw [hbb, mul_one] at hinner
  have hzz : ⟪ψ, φ⟫_ℂ * (⟪ψ, φ⟫_ℂ - 1) = 0 := by
    rw [mul_sub, mul_one, hinner, sub_self]
  rcases mul_eq_zero.mp hzz with hz | hz
  · rw [hz, norm_zero] at hpos
    exact lt_irrefl _ hpos
  · have h1 : ⟪ψ, φ⟫_ℂ = 1 := sub_eq_zero.mp hz
    rw [h1, norm_one] at hlt
    exact lt_irrefl _ hlt

/-- **No-cloning theorem (linear form).** Let `H` be a complex inner-product space containing two
orthonormal vectors `e₁` and `e₂`, and let `b ∈ H` be any blank state. Then no `ℂ`-linear map
`U : H ⊗ H → H ⊗ H` satisfies `U (ψ ⊗ b) = ψ ⊗ ψ` for every unit vector `ψ`. Linearity alone
forbids it: for `φ = (e₁ + e₂) / √2`, linearity gives
`U (φ ⊗ b) = (e₁ ⊗ e₁ + e₂ ⊗ e₂) / √2`, which has no `e₁ ⊗ e₂` component, while `φ ⊗ φ` does.
Unitarity is not used, so the statement covers every isometry and every unitary.
Source: W. K. Wootters and W. H. Zurek, "A single quantum cannot be cloned",
Nature 299 (1982), 802-803, DOI 10.1038/299802a0 (the linearity argument). -/
public theorem no_cloning_linear
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e₁ e₂ b : H)
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫_ℂ = 0) :
    ¬ ∃ U : (H ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] H),
      ∀ ψ : H, ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] b) = ψ ⊗ₜ[ℂ] ψ := by
  rintro ⟨U, hU⟩
  have h11 : ⟪e₁, e₁⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, h₁]; norm_num
  have h22 : ⟪e₂, e₂⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, h₂]; norm_num
  have h21 : ⟪e₂, e₁⟫_ℂ = 0 := by rw [← inner_conj_symm, h₁₂, map_zero]
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  set c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact inv_ne_zero (by exact_mod_cast hs.ne')
  set φ : H := c • (e₁ + e₂) with hφ
  have hsum : ‖e₁ + e₂‖ = Real.sqrt 2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), sq,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h₁₂, h₁, h₂]
    norm_num
  have hnorm : ‖φ‖ = 1 := by
    rw [hφ, norm_smul, hsum, hc, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs, inv_mul_cancel₀ hs.ne']
  -- Linearity: `U (φ ⊗ b) = (c • e₁) ⊗ e₁ + (c • e₂) ⊗ e₂`.
  have hlin : U (φ ⊗ₜ[ℂ] b) = (c • e₁) ⊗ₜ[ℂ] e₁ + (c • e₂) ⊗ₜ[ℂ] e₂ := by
    rw [hφ, smul_add, add_tmul, map_add, ← smul_tmul', ← smul_tmul', map_smul, map_smul,
      hU e₁ h₁, hU e₂ h₂, smul_tmul', smul_tmul']
  have hcl := hU φ hnorm
  rw [hlin] at hcl
  -- Compare the `e₁ ⊗ e₂` components: `0 = c * c`.
  have key := congrArg (fun z => ⟪e₁ ⊗ₜ[ℂ] e₂, z⟫_ℂ) hcl
  simp only [hφ, inner_smul_right, inner_add_right, TensorProduct.inner_tmul,
    h11, h22, h₁₂, h21] at key
  apply hc0
  have : c * c = 0 := by linear_combination -key
  exact mul_self_eq_zero.1 this

end MathlibExt.QuantumInformation.Finite.NoCloning
