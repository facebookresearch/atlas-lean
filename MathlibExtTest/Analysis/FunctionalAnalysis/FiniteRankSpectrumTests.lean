/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.FiniteRankSpectrum

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Tests for the spectrum of finite-rank operators

Two concrete finite-rank operators on `ℓ²(ℕ, ℂ)`:

* the rank-one projection `rankOne e₀ e₀` onto the first coordinate, whose
  spectrum is `{0, 1}`;
* the operator `rankOne e₀ e₀ + 2 • rankOne e₁ e₁`, whose spectrum is
  `{0, 1, 2}`.

The tests exercise the eigenvalue-count bound, the finiteness of the
spectrum, the `ncard ≤ finrank + 1` bound, and the exact spectrum on an
infinite-dimensional space.
-/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.FiniteRankSpectrumTests

open scoped _root_.InnerProductSpace
open MathlibExt.Analysis.FunctionalAnalysis.FiniteRankSpectrum

/-- The first standard basis vector of `ℓ²(ℕ, ℂ)`. -/
private noncomputable abbrev e₀ : lp (fun _ : ℕ => ℂ) 2 := lp.single 2 0 1

/-- The second standard basis vector of `ℓ²(ℕ, ℂ)`. -/
private noncomputable abbrev e₁ : lp (fun _ : ℕ => ℂ) 2 := lp.single 2 1 1

/-- The rank-one projection onto the first coordinate of `ℓ²(ℕ, ℂ)`. -/
noncomputable def projE0 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  InnerProductSpace.rankOne ℂ e₀ e₀

/-- The operator on `ℓ²(ℕ, ℂ)` with eigenvalues `1` and `2` on the first two
coordinates and `0` elsewhere. -/
noncomputable def twoEigOp : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  InnerProductSpace.rankOne ℂ e₀ e₀ +
    (2 : ℂ) • InnerProductSpace.rankOne ℂ e₁ e₁

/-- The inner product `⟪e₀, e₀⟫` is `1`. -/
theorem inner_single_single (i j : ℕ) :
    ⟪(lp.single 2 i (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2),
      (lp.single 2 j (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)⟫_ℂ =
      if i = j then 1 else 0 := by
  rw [lp.inner_single_left, lp.single_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- The inner product `⟪e₀, e₀⟫` is `1`. -/
theorem inner_e0_e0 : ⟪e₀, e₀⟫_ℂ = 1 := by
  simp [e₀]

/-- The inner product `⟪e₁, e₁⟫` is `1`. -/
theorem inner_e1_e1 : ⟪e₁, e₁⟫_ℂ = 1 := by
  simp [e₁]

/-- The inner product `⟪e₀, e₁⟫` is `0`. -/
theorem inner_e0_e1 : ⟪e₀, e₁⟫_ℂ = 0 := by
  simp [e₀, e₁, inner_single_single]

/-- The inner product `⟪e₁, e₀⟫` is `0`. -/
theorem inner_e1_e0 : ⟪e₁, e₀⟫_ℂ = 0 := by
  simp [e₁, e₀, inner_single_single]

/-- The first two standard basis vectors are distinct. -/
theorem e0_ne_e1 : e₀ ≠ e₁ := by
  intro h
  have h0 := congrArg (fun x : lp (fun _ : ℕ => ℂ) 2 ↦ x 0) h
  simp [e₀, e₁] at h0

/-- The first standard basis vector is nonzero. -/
theorem e0_ne_zero : e₀ ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : lp (fun _ : ℕ => ℂ) 2 ↦ x 0) h
  simp [e₀] at h0

/-- The second standard basis vector is nonzero. -/
theorem e1_ne_zero : e₁ ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : lp (fun _ : ℕ => ℂ) 2 ↦ x 1) h
  simp [e₁] at h0

/-- The action of `twoEigOp` on a vector, in coordinates. -/
theorem apply_twoEigOp (v : lp (fun _ : ℕ => ℂ) 2) :
    (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) v =
      ⟪e₀, v⟫_ℂ • e₀ + (2 * ⟪e₁, v⟫_ℂ) • e₁ := by
  simp only [twoEigOp, ContinuousLinearMap.coe_coe, add_apply,
    smul_apply, InnerProductSpace.rankOne_apply, smul_smul]

/-- `twoEigOp` fixes the first basis vector. -/
theorem apply_twoEigOp_e0 : (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
    lp (fun _ : ℕ => ℂ) 2) e₀ = e₀ := by
  rw [apply_twoEigOp]
  simp [inner_e1_e0]

/-- `twoEigOp` sends the second basis vector to twice itself. -/
theorem apply_twoEigOp_e1 : (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
    lp (fun _ : ℕ => ℂ) 2) e₁ = (2 : ℂ) • e₁ := by
  rw [apply_twoEigOp]
  simp [inner_e0_e1]

/-- `twoEigOp` sends `(1 / 2) • e₁` to `e₁`, so `e₁` is in the range. -/
theorem apply_twoEigOp_half_e1 : (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
    lp (fun _ : ℕ => ℂ) 2) ((1 / 2 : ℂ) • e₁) = e₁ := by
  rw [apply_twoEigOp]
  simp [inner_e0_e1, inner_smul_right]

/-- The range of `twoEigOp` is the span of the first two basis vectors. -/
theorem range_twoEigOp_eq_span :
    LinearMap.range (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) =
      Submodule.span ℂ {e₀, e₁} := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [apply_twoEigOp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨e₀, apply_twoEigOp_e0⟩
    · exact ⟨(1 / 2 : ℂ) • e₁, apply_twoEigOp_half_e1⟩

/-- The range of `twoEigOp` is finite-dimensional. -/
theorem finiteDimensional_range_twoEigOp :
    FiniteDimensional ℂ (LinearMap.range (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
      lp (fun _ : ℕ => ℂ) 2)) := by
  rw [range_twoEigOp_eq_span]
  exact FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton _).insert _)

/-- The rank of `twoEigOp` is at most `2`. -/
theorem finrank_range_twoEigOp_le :
    Module.finrank ℂ (LinearMap.range (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
      lp (fun _ : ℕ => ℂ) 2)) ≤ 2 := by
  rw [range_twoEigOp_eq_span]
  have hFintype : Fintype ↥({e₀, e₁} : Set (lp (fun _ : ℕ => ℂ) 2)) :=
    ((Set.finite_singleton _).insert _).fintype
  have h := finrank_span_le_card (R := ℂ) (M := lp (fun _ : ℕ => ℂ) 2)
    (s := {e₀, e₁})
  have hcard : ({e₀, e₁} : Set (lp (fun _ : ℕ => ℂ) 2)).toFinset.card = 2 := by
    simp [e0_ne_e1]
  rw [hcard] at h
  exact h

/-- The range of `projE0` is the span of the first basis vector. -/
theorem range_projE0_eq_span :
    LinearMap.range (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) =
      Submodule.span ℂ {e₀} := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    simp only [projE0, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨e₀, ?_⟩
    simp only [projE0, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      inner_e0_e0, one_smul]

/-- The range of `projE0` is finite-dimensional. -/
theorem finiteDimensional_range_projE0 :
    FiniteDimensional ℂ (LinearMap.range (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
      lp (fun _ : ℕ => ℂ) 2)) := by
  rw [range_projE0_eq_span]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)

/-- The rank of `projE0` is at most `1`. -/
theorem finrank_range_projE0_le :
    Module.finrank ℂ (LinearMap.range (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
      lp (fun _ : ℕ => ℂ) 2)) ≤ 1 := by
  rw [range_projE0_eq_span]
  have hFintype : Fintype ↥({e₀} : Set (lp (fun _ : ℕ => ℂ) 2)) :=
    (Set.finite_singleton _).fintype
  have h := finrank_span_le_card (R := ℂ) (M := lp (fun _ : ℕ => ℂ) 2)
    (s := {e₀})
  have hcard : ({e₀} : Set (lp (fun _ : ℕ => ℂ) 2)).toFinset.card = 1 := by
    simp
  rw [hcard] at h
  exact h

/-- `ℓ²(ℕ, ℂ)` is infinite-dimensional: the standard basis vectors are
orthonormal, hence linearly independent, but `ℕ` is infinite. -/
theorem not_finiteDimensional_lp :
    ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) := by
  intro hFin
  have : Module.Finite ℂ (lp (fun _ : ℕ => ℂ) 2) := hFin
  have horth : Orthonormal ℂ (fun n : ℕ ↦ lp.single 2 n (1 : ℂ)) := by
    rw [orthonormal_iff_ite]
    intro i j
    exact inner_single_single i j
  have hli := horth.linearIndependent
  have hcard := hli.lt_aleph0_of_finite
  rw [Cardinal.mk_nat] at hcard
  exact lt_irrefl _ hcard

/-- A nonzero eigenvalue of `twoEigOp` is `1` or `2`. -/
theorem eigenvalue_twoEigOp_eq {μ : ℂ} (hμ : μ ≠ 0)
    (h : Module.End.HasEigenvalue
      (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) μ) :
    μ = 1 ∨ μ = 2 := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hTv : (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) v =
      μ • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hinner0 : ⟪e₀, (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
      lp (fun _ : ℕ => ℂ) 2) v⟫_ℂ = ⟪e₀, v⟫_ℂ := by
    rw [apply_twoEigOp]
    simp [inner_add_right, inner_smul_right, inner_e0_e1]
  have hinner1 : ⟪e₁, (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
      lp (fun _ : ℕ => ℂ) 2) v⟫_ℂ = 2 * ⟪e₁, v⟫_ℂ := by
    rw [apply_twoEigOp]
    simp [inner_add_right, inner_smul_right, inner_e1_e0]
  have hμ0 : μ * ⟪e₀, v⟫_ℂ = ⟪e₀, v⟫_ℂ := by
    have h := congrArg (fun w ↦ ⟪e₀, w⟫_ℂ) hTv
    rw [hinner0, inner_smul_right] at h
    exact h.symm
  have hμ1 : μ * ⟪e₁, v⟫_ℂ = 2 * ⟪e₁, v⟫_ℂ := by
    have h := congrArg (fun w ↦ ⟪e₁, w⟫_ℂ) hTv
    rw [hinner1, inner_smul_right] at h
    exact h.symm
  have h0 : (μ - 1) * ⟪e₀, v⟫_ℂ = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hμ0
  have h1 : (μ - 2) * ⟪e₁, v⟫_ℂ = 0 := by
    rw [sub_mul]
    have h2 : (2 : ℂ) * ⟪e₁, v⟫_ℂ = 2 * ⟪e₁, v⟫_ℂ := rfl
    rw [h2]
    exact sub_eq_zero.mpr hμ1
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact Or.inl (sub_eq_zero.mp h0)
  · rcases mul_eq_zero.mp h1 with h1 | h1
    · exact Or.inr (sub_eq_zero.mp h1)
    · exfalso
      have hTv0 : (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) v = 0 := by
        rw [apply_twoEigOp, h0, h1]
        simp
      rw [hTv] at hTv0
      exact hv.2 (smul_eq_zero.mp hTv0 |>.resolve_left hμ)

/-- `1` is an eigenvalue of `twoEigOp`. -/
theorem hasEigenvalue_one_twoEigOp : Module.End.HasEigenvalue
    (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) 1 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, e0_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff, apply_twoEigOp_e0]
  simp

/-- `2` is an eigenvalue of `twoEigOp`. -/
theorem hasEigenvalue_two_twoEigOp : Module.End.HasEigenvalue
    (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) 2 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, e1_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff, apply_twoEigOp_e1]

/-- **The spectrum of `twoEigOp` is exactly `{0, 1, 2}`.** -/
example : spectrum ℂ twoEigOp = {0, 1, 2} := by
  rw [spectrum_eq_insert_zero_hasEigenvalue finiteDimensional_range_twoEigOp
    not_finiteDimensional_lp]
  apply Set.Subset.antisymm
  · intro μ hμ
    rw [Set.mem_insert_iff] at hμ
    rcases hμ with rfl | hμ
    · simp
    · by_cases hμ0 : μ = 0
      · subst hμ0
        simp
      · rcases eigenvalue_twoEigOp_eq hμ0 hμ with rfl | rfl <;> simp
  · intro μ hμ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ ⊢
    rcases hμ with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hasEigenvalue_one_twoEigOp
    · exact Or.inr hasEigenvalue_two_twoEigOp

/-- The spectrum of `twoEigOp` is finite, with at most `3` points. -/
example : (spectrum ℂ twoEigOp).Finite :=
  finite_spectrum_of_finiteDimensional_range finiteDimensional_range_twoEigOp

/-- The spectrum of `twoEigOp` has at most `finrank + 1 = 3` points. -/
example : (spectrum ℂ twoEigOp).ncard ≤ 3 :=
  le_trans
    (ncard_spectrum_le_finrank_range_add_one finiteDimensional_range_twoEigOp)
    (by have h := finrank_range_twoEigOp_le; omega)

/-- The nonzero eigenvalues of `twoEigOp` number at most `2`. -/
example : ({μ | Module.End.HasEigenvalue
    (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) μ ∧ μ ≠ 0} :
    Set ℂ).ncard ≤ 2 :=
  le_trans
    (Module.End.ncard_nonzero_hasEigenvalue_le_finrank_range
      (T := (twoEigOp : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2))
      finiteDimensional_range_twoEigOp)
    finrank_range_twoEigOp_le

/-- A nonzero eigenvalue of `projE0` is `1`. -/
theorem eigenvalue_projE0_eq {μ : ℂ} (hμ : μ ≠ 0)
    (h : Module.End.HasEigenvalue
      (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) μ) :
    μ = 1 := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hTv : (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) v =
      μ • v := Module.End.mem_eigenspace_iff.mp hv.1
  have happly : (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) v =
      ⟪e₀, v⟫_ℂ • e₀ := by
    simp only [projE0, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
  have hμ0 : μ * ⟪e₀, v⟫_ℂ = ⟪e₀, v⟫_ℂ := by
    have h := congrArg (fun w ↦ ⟪e₀, w⟫_ℂ) hTv
    rw [happly, inner_smul_right, inner_e0_e0, mul_one] at h
    rw [inner_smul_right] at h
    exact h.symm
  have h0 : (μ - 1) * ⟪e₀, v⟫_ℂ = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hμ0
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have hTv0 : (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) v = 0 := by
      rw [happly, h0]
      simp
    rw [hTv] at hTv0
    exact hv.2 (smul_eq_zero.mp hTv0 |>.resolve_left hμ)

/-- `1` is an eigenvalue of `projE0`. -/
theorem hasEigenvalue_one_projE0 : Module.End.HasEigenvalue
    (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) 1 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, e0_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff]
  simp only [projE0, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    inner_e0_e0, one_smul]

/-- **The spectrum of `projE0` is exactly `{0, 1}`.** -/
example : spectrum ℂ projE0 = {0, 1} := by
  rw [spectrum_eq_insert_zero_hasEigenvalue finiteDimensional_range_projE0
    not_finiteDimensional_lp]
  apply Set.Subset.antisymm
  · intro μ hμ
    rw [Set.mem_insert_iff] at hμ
    rcases hμ with rfl | hμ
    · simp
    · by_cases hμ0 : μ = 0
      · subst hμ0
        simp
      · have h1 := eigenvalue_projE0_eq hμ0 hμ
        rw [h1]
        simp
  · intro μ hμ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ ⊢
    rcases hμ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hasEigenvalue_one_projE0

/-- The nonzero eigenvalues of `projE0` number at most `1`. -/
example : ({μ | Module.End.HasEigenvalue
    (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) μ ∧ μ ≠ 0} :
    Set ℂ).ncard ≤ 1 :=
  le_trans
    (Module.End.ncard_nonzero_hasEigenvalue_le_finrank_range
      (T := (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2))
      finiteDimensional_range_projE0)
    finrank_range_projE0_le

/-- The chosen family exposes an actual eigenvector at the nonzero eigenvalue 1. -/
theorem chosen_family_has_eigenvector_one :
    ∃ xs : {μ // Module.End.HasEigenvalue
        (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) μ ∧ μ ≠ 0} →
        lp (fun _ : ℕ => ℂ) 2,
      LinearIndependent ℂ xs ∧
        (∀ μ, xs μ ∈ LinearMap.range
          (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2)) ∧
        Module.End.HasEigenvector
          (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) 1
          (xs ⟨1, hasEigenvalue_one_projE0, by norm_num⟩) := by
  obtain ⟨xs, hli, hmem, heigen⟩ :=
    Module.End.exists_linearIndependent_eigenvectors
      (T := (projE0 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2))
  exact ⟨xs, hli, hmem, heigen ⟨1, hasEigenvalue_one_projE0, by norm_num⟩⟩

end MathlibExtTest.Analysis.FunctionalAnalysis.FiniteRankSpectrumTests
