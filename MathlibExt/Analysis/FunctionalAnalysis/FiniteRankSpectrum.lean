/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorNotUnit
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Choose

/-!
# Spectrum of finite-rank operators

A linear operator `T` has finite rank if its range is finite-dimensional.
The point of this file is that such an operator has very little spectrum:
its nonzero eigenvalues are the only possible nonzero spectral values, and
there are at most `finrank (range T)` of them, because eigenvectors for
distinct eigenvalues are linearly independent and all lie in the range.
In particular the spectrum is finite, and on an infinite-dimensional space
it is exactly `{0} ∪ {eigenvalues}`.

This is a companion to the spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the Fredholm alternative for compact self-adjoint operators and the spectral
theorem for compact self-adjoint operators), not one of the 72 v1 targets:
v1 never discusses finite-rank operators. The spectrum statements use
Mathlib's Fredholm alternative for compact operators
(`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`); the new content is the
finite-rank compactness (factorization through the finite-dimensional range)
and the eigenvalue-count bound, which is neither in the pinned Mathlib nor in
base MathlibExt: Mathlib has the per-eigenspace finiteness for compact
self-adjoint operators and the statement that the eigenvalues of a compact
operator accumulate only at `0`, but no bound on the number of distinct
nonzero eigenvalues of a finite-rank operator, and no finiteness of its
spectrum. See e.g. Reed–Simon, *Methods of Modern Mathematical Physics I:
Functional Analysis*, Theorem VI.14, for the classical statements.

## Main declarations

* `Module.End.eigenvector_mem_range_of_hasEigenvector` : an eigenvector for a
  nonzero eigenvalue lies in the range.
* `Module.End.exists_linearIndependent_eigenvectors` : one eigenvector per
  nonzero eigenvalue, forming a linearly independent family in the range.
* `Module.End.finite_nonzero_hasEigenvalue_of_finiteDimensional_range` : the
  set of nonzero eigenvalues of a finite-rank operator is finite.
* `Module.End.ncard_nonzero_hasEigenvalue_le_finrank_range` : there are at
  most `finrank (range T)` distinct nonzero eigenvalues.
* `isCompactOperator_of_finiteDimensional_range` : a finite-rank operator is
  compact.
* `spectrum_subset_insert_zero_hasEigenvalue` : the spectrum is contained in
  `{0} ∪ {eigenvalues}`.
* `finite_spectrum_of_finiteDimensional_range` : the spectrum of a
  finite-rank operator is finite.
* `ncard_spectrum_le_finrank_range_add_one` : the spectrum has at most
  `finrank (range T) + 1` points.
* `spectrum_eq_insert_zero_hasEigenvalue` : on an infinite-dimensional space,
  the spectrum is exactly `{0} ∪ {eigenvalues}`.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.FiniteRankSpectrum

section LinearAlgebra

variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {T : Module.End 𝕜 E}

/-- An eigenvector for a nonzero eigenvalue lies in the range: if
`T v = μ • v` with `μ ≠ 0`, then `v = T (μ⁻¹ • v)`. -/
theorem Module.End.eigenvector_mem_range_of_hasEigenvector {μ : 𝕜} {v : E}
    (h : T.HasEigenvector μ v) (hμ : μ ≠ 0) : v ∈ LinearMap.range T := by
  have hTv : T v = μ • v := Module.End.mem_eigenspace_iff.mp h.1
  refine ⟨μ⁻¹ • v, ?_⟩
  rw [map_smul, hTv, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- Choose one eigenvector for each nonzero eigenvalue of `T`. The chosen
eigenvectors are linearly independent (eigenvectors for distinct eigenvalues)
and all lie in the range of `T`. -/
theorem Module.End.exists_linearIndependent_eigenvectors :
    ∃ xs : {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} → E,
      LinearIndependent 𝕜 xs ∧
        (∀ μ, xs μ ∈ LinearMap.range T) ∧
        ∀ μ : {μ // T.HasEigenvalue μ ∧ μ ≠ 0}, T.HasEigenvector (μ : 𝕜) (xs μ) := by
  have hex : ∀ μ : {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0},
      ∃ v, T.HasEigenvector μ v := by
    intro μ
    exact μ.2.1.exists_hasEigenvector
  choose xs hxs using hex
  refine ⟨xs, Module.End.eigenvectors_linearIndependent T _ xs hxs, (fun μ ↦ ?_), hxs⟩
  exact Module.End.eigenvector_mem_range_of_hasEigenvector (hxs μ) μ.2.2

/-- **Eigenvalue finiteness for finite-rank operators.** A finite-rank
operator has only finitely many distinct nonzero eigenvalues. -/
theorem Module.End.finite_nonzero_hasEigenvalue_of_finiteDimensional_range
    (hF : FiniteDimensional 𝕜 (LinearMap.range T)) :
    ({μ | Module.End.HasEigenvalue T μ ∧ μ ≠ 0} : Set 𝕜).Finite := by
  have : FiniteDimensional 𝕜 (LinearMap.range T) := hF
  obtain ⟨xs, hli, hmem, _⟩ := Module.End.exists_linearIndependent_eigenvectors (T := T)
  have hli_w : LinearIndependent 𝕜
      (fun μ : {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} ↦
        (⟨xs μ, hmem μ⟩ : LinearMap.range T)) := by
    apply LinearIndependent.of_comp (LinearMap.range T).subtype
    rw [show (LinearMap.range T).subtype ∘
        (fun μ : {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} ↦
          (⟨xs μ, hmem μ⟩ : LinearMap.range T)) =
        xs from rfl]
    exact hli
  have hcard : Cardinal.mk {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} <
      Cardinal.aleph0 :=
    hli_w.lt_aleph0_of_finite
  exact Set.finite_coe_iff.mp (Cardinal.lt_aleph0_iff_finite.mp hcard)

/-- **Eigenvalue-count bound for finite-rank operators.** There are at most
`finrank (range T)` distinct nonzero eigenvalues. -/
theorem Module.End.ncard_nonzero_hasEigenvalue_le_finrank_range
    (hF : FiniteDimensional 𝕜 (LinearMap.range T)) :
    ({μ | Module.End.HasEigenvalue T μ ∧ μ ≠ 0} : Set 𝕜).ncard ≤
      Module.finrank 𝕜 (LinearMap.range T) := by
  have : FiniteDimensional 𝕜 (LinearMap.range T) := hF
  have hfin := Module.End.finite_nonzero_hasEigenvalue_of_finiteDimensional_range
    (T := T) hF
  have hFiniteSub : Finite {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} :=
    Set.finite_coe_iff.mpr hfin
  have hFintypeSub : Fintype {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} :=
    Fintype.ofFinite _
  obtain ⟨xs, hli, hmem, _⟩ := Module.End.exists_linearIndependent_eigenvectors (T := T)
  have hli_w : LinearIndependent 𝕜
      (fun μ : {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} ↦
        (⟨xs μ, hmem μ⟩ : LinearMap.range T)) := by
    apply LinearIndependent.of_comp (LinearMap.range T).subtype
    rw [show (LinearMap.range T).subtype ∘
        (fun μ : {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} ↦
          (⟨xs μ, hmem μ⟩ : LinearMap.range T)) =
        xs from rfl]
    exact hli
  calc ({μ | Module.End.HasEigenvalue T μ ∧ μ ≠ 0} : Set 𝕜).ncard
      = Fintype.card {μ // Module.End.HasEigenvalue T μ ∧ μ ≠ 0} :=
        (@Set.fintypeCard_eq_ncard 𝕜 _ hFintypeSub).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range T) := hli_w.fintype_card_le_finrank

end LinearAlgebra

section Compactness

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {T : E →L[𝕜] E}

/-- A finite-rank operator is compact: it factors through its
finite-dimensional range, and every continuous linear map out of a
finite-dimensional (hence locally compact) space is compact. -/
theorem isCompactOperator_of_finiteDimensional_range
    (hF : FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E))) :
    IsCompactOperator T := by
  have : FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E)) := hF
  have hproper : ProperSpace ↥(LinearMap.range (T : E →ₗ[𝕜] E)) :=
    FiniteDimensional.proper 𝕜 _
  have hloc : LocallyCompactSpace ↥(LinearMap.range (T : E →ₗ[𝕜] E)) :=
    locallyCompact_of_proper
  have hsub : IsCompactOperator
      (LinearMap.range (T : E →ₗ[𝕜] E)).subtypeL :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have hT : IsCompactOperator
      ((LinearMap.range (T : E →ₗ[𝕜] E)).subtypeL ∘
        T.codRestrict (LinearMap.range (T : E →ₗ[𝕜] E))
          (fun x ↦ LinearMap.mem_range_self _ x)) :=
    hsub.comp_clm _
  have hEq : (LinearMap.range (T : E →ₗ[𝕜] E)).subtypeL ∘
        T.codRestrict (LinearMap.range (T : E →ₗ[𝕜] E))
          (fun x ↦ LinearMap.mem_range_self _ x) = T := by
    funext x
    rfl
  rw [hEq] at hT
  exact hT

end Compactness

section Spectrum

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] {T : E →L[𝕜] E}

/-- The spectrum of a finite-rank operator is contained in
`{0} ∪ {eigenvalues}`: every nonzero spectral value is an eigenvalue, by
the Fredholm alternative for compact operators. -/
theorem spectrum_subset_insert_zero_hasEigenvalue
    (hF : FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E))) :
    spectrum 𝕜 T ⊆ insert 0
      {μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ} := by
  intro μ hμ
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  · have hcomp := isCompactOperator_of_finiteDimensional_range (T := T) hF
    have hiff := IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcomp hμ0
    rw [Set.mem_insert_iff]
    exact Or.inr (hiff.mpr hμ)

/-- Every eigenvalue of a finite-rank operator lies in its spectrum. -/
theorem hasEigenvalue_subset_spectrum :
    {μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ} ⊆ spectrum 𝕜 T := by
  intro μ hμ
  rw [ContinuousLinearMap.spectrum_eq]
  exact Module.End.HasEigenvalue.mem_spectrum hμ

/-- The spectrum of a finite-rank operator is finite. -/
theorem finite_spectrum_of_finiteDimensional_range
    (hF : FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E))) :
    (spectrum 𝕜 T).Finite := by
  have hfin := Module.End.finite_nonzero_hasEigenvalue_of_finiteDimensional_range
    (T := (T : E →ₗ[𝕜] E)) hF
  have hsub := spectrum_subset_insert_zero_hasEigenvalue (T := T) hF
  have hsub' : spectrum 𝕜 T ⊆
      insert 0 {μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ μ ≠ 0} := by
    intro μ hμ
    have hμ' := hsub hμ
    rw [Set.mem_insert_iff] at hμ' ⊢
    rcases hμ' with h | h
    · exact Or.inl h
    · by_cases hμ0 : μ = 0
      · exact Or.inl hμ0
      · exact Or.inr ⟨h, hμ0⟩
  exact (hfin.insert 0).subset hsub'

/-- The spectrum of a finite-rank operator has at most
`finrank (range T) + 1` points. -/
theorem ncard_spectrum_le_finrank_range_add_one
    (hF : FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E))) :
    (spectrum 𝕜 T).ncard ≤ Module.finrank 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E)) + 1 := by
  have hfinIns : (insert 0
      {μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ μ ≠ 0} : Set 𝕜).Finite :=
    (Module.End.finite_nonzero_hasEigenvalue_of_finiteDimensional_range
      (T := (T : E →ₗ[𝕜] E)) hF).insert 0
  have hsub : spectrum 𝕜 T ⊆
      insert 0 {μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ μ ≠ 0} := by
    intro μ hμ
    have hμ' := (spectrum_subset_insert_zero_hasEigenvalue (T := T) hF) hμ
    rw [Set.mem_insert_iff] at hμ' ⊢
    rcases hμ' with h | h
    · exact Or.inl h
    · by_cases hμ0 : μ = 0
      · exact Or.inl hμ0
      · exact Or.inr ⟨h, hμ0⟩
  calc (spectrum 𝕜 T).ncard
      ≤ (insert 0 {μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ μ ≠ 0}).ncard :=
        Set.ncard_le_ncard hsub hfinIns
    _ ≤ ({μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ μ ≠ 0} : Set 𝕜).ncard + 1 :=
        Set.ncard_insert_le _ _
    _ ≤ Module.finrank 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E)) + 1 := by
        exact Nat.add_le_add_right
          (Module.End.ncard_nonzero_hasEigenvalue_le_finrank_range (T := (T : E →ₗ[𝕜] E)) hF) 1

/-- **Spectrum of a finite-rank operator on an infinite-dimensional space.**
The spectrum is exactly `{0} ∪ {eigenvalues}`. -/
theorem spectrum_eq_insert_zero_hasEigenvalue
    (hF : FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] E)))
    (hInf : ¬ FiniteDimensional 𝕜 E) :
    spectrum 𝕜 T = insert 0
      {μ | Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ} := by
  apply Set.Subset.antisymm
  · exact spectrum_subset_insert_zero_hasEigenvalue hF
  · intro μ hμ
    rw [Set.mem_insert_iff] at hμ
    rcases hμ with h | h
    · rw [h]
      exact CompactOperatorNotUnit.zero_mem_spectrum_of_isCompactOperator hInf T
        (isCompactOperator_of_finiteDimensional_range hF)
    · exact hasEigenvalue_subset_spectrum h

end Spectrum

end MathlibExt.Analysis.FunctionalAnalysis.FiniteRankSpectrum
