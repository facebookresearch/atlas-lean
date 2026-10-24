/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorEigenvalues

@[expose] public section

open Function Set Filter Topology
open Module End
open MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorEigenvalues

namespace MathlibExtTest.Analysis.FunctionalAnalysis.CompactOperatorEigenvalues

/-!
# Tests for eigenvalues of compact operators

The abstract examples check the theorems on a hypothetical compact operator.
The finite-dimensional examples are concrete: the identity operator on
`Fin 2 → ℝ` is compact, its eigenvalue set above `1 / 2` is exactly
`{1}` (so finiteness is not vacuous), and above `2` it is empty.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Eigenvalues of a compact operator bounded away from zero are finite. -/
example (T : E →L[𝕜] E) (hc : IsCompactOperator (T : E → E)) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : 𝕜 | Module.End.HasEigenvalue (T.toLinearMap) μ ∧ ε ≤ ‖μ‖} :=
  finite_eigenvalues_of_ge hc hε

/-- An injective sequence of eigenvalues of a compact operator tends to zero. -/
example (T : E →L[𝕜] E) (hc : IsCompactOperator (T : E → E)) {lam : ℕ → 𝕜}
    (hinj : Function.Injective lam)
    (hlam : ∀ n, Module.End.HasEigenvalue (T.toLinearMap) (lam n)) :
    Tendsto lam atTop (𝓝 0) :=
  tendsto_eigenvalue_of_injective hc hinj hlam

/-- The identity operator on `Fin 2 → ℝ` is compact. -/
example : IsCompactOperator
    ((1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) : (Fin 2 → ℝ) → (Fin 2 → ℝ)) := by
  have hcoe : ((1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :
      (Fin 2 → ℝ) → (Fin 2 → ℝ)) = id := by
    funext x
    rfl
  rw [hcoe]
  exact isCompactOperator_id

/-- The only eigenvalue of the identity operator on `Fin 2 → ℝ` is `1`. -/
theorem hasEigenvalue_one_iff {μ : ℝ} :
    Module.End.HasEigenvalue
      ((1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).toLinearMap) μ ↔ μ = 1 := by
  constructor
  · intro hμ
    by_contra hne
    obtain ⟨x, hx_mem, hx_ne⟩ := hμ.exists_hasEigenvector
    have hx_eq : x = μ • x := by
      have h := Module.End.mem_eigenspace_iff.mp hx_mem
      exact h
    have h1 : (1 - μ) • x = 0 := by
      rw [sub_smul, one_smul, ← hx_eq, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact hne (by linarith [sub_eq_zero.mp h])
    · exact hx_ne h
  · intro h
    rw [h, Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
    refine ⟨fun _ => (1 : ℝ), ?_, ?_⟩
    · exact Module.End.mem_eigenspace_iff.mpr (by simp)
    · intro hzero
      have h0 := congrFun hzero 0
      simp at h0

/-- For the identity on `Fin 2 → ℝ`, the eigenvalues above `1 / 2` are
exactly `{1}`: `1` is an eigenvalue, and no other scalar is. -/
example : {μ : ℝ | Module.End.HasEigenvalue
      ((1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).toLinearMap) μ ∧ (1 / 2 : ℝ) ≤ ‖μ‖}
    = {1} := by
  ext μ
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hasEigenvalue_one_iff]
  constructor
  · intro h
    exact h.1
  · intro h
    rw [h]
    norm_num

/-- For the identity on `Fin 2 → ℝ`, no eigenvalue is above `2`,
so the eigenvalue set above `2` is empty (hence finite). -/
example : {μ : ℝ | Module.End.HasEigenvalue
      ((1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).toLinearMap) μ ∧ (2 : ℝ) ≤ ‖μ‖}
    = ∅ := by
  ext μ
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h
  rw [hasEigenvalue_one_iff] at h
  rw [h]
  norm_num

end MathlibExtTest.Analysis.FunctionalAnalysis.CompactOperatorEigenvalues
