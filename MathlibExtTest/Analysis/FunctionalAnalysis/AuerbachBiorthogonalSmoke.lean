/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

import MathlibExt.Analysis.FunctionalAnalysis.AuerbachBasis
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open MathlibExt.Analysis.FunctionalAnalysis.AuerbachBasis

-- Recover nonreal and negative coordinates of a vector in the same Auerbach basis.
example :
    ∃ (b : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
      (φ : Fin 2 → EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ),
      (∀ i, ‖b i‖ = 1) ∧ (∀ i, ‖φ i‖ = 1) ∧
        φ 0 (((2 : ℂ) + Complex.I) • b 0 - (3 : ℂ) • b 1) = 2 + Complex.I ∧
        φ 1 (((2 : ℂ) + Complex.I) • b 0 - (3 : ℂ) • b 1) = -3 := by
  have h : ∃ (b : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
      (φ : Fin 2 → EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ),
      (∀ i, ‖b i‖ = 1) ∧ (∀ i, ‖φ i‖ = 1) ∧
        ∀ i j, φ i (b j) = if i = j then 1 else 0 := by
    have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 := by
      simpa only [Fintype.card_fin] using
        (Module.finrank_eq_card_basis (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis)
    have h := exists_auerbach_basis_biorthogonal
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin 2))
    rw [hdim] at h
    exact h
  obtain ⟨b, φ, hb, hφ, hδ⟩ := h
  refine ⟨b, φ, hb, hφ, ?_, ?_⟩
  · simp [map_sub, map_smul, hδ, smul_eq_mul]
  · simp [map_sub, map_smul, hδ, smul_eq_mul]

-- The empty family is available without a Nontrivial instance on its coefficient space.
example :
    ∃ (b : Module.Basis (Fin 0) ℂ (EuclideanSpace ℂ (Fin 0)))
      (φ : Fin 0 → EuclideanSpace ℂ (Fin 0) →L[ℂ] ℂ),
      (∀ i, ‖b i‖ = 1) ∧ (∀ i, ‖φ i‖ = 1) ∧
        ∀ x : EuclideanSpace ℂ (Fin 0), x = 0 := by
  have h : ∃ (b : Module.Basis (Fin 0) ℂ (EuclideanSpace ℂ (Fin 0)))
      (φ : Fin 0 → EuclideanSpace ℂ (Fin 0) →L[ℂ] ℂ),
      (∀ i, ‖b i‖ = 1) ∧ (∀ i, ‖φ i‖ = 1) ∧
        ∀ i j, φ i (b j) = if i = j then 1 else 0 := by
    have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) = 0 := by
      simpa only [Fintype.card_fin] using
        (Module.finrank_eq_card_basis (EuclideanSpace.basisFun (Fin 0) ℂ).toBasis)
    have h := exists_auerbach_basis_biorthogonal
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin 0))
    rw [hdim] at h
    exact h
  obtain ⟨b, φ, hb, hφ, _⟩ := h
  exact ⟨b, φ, hb, hφ, fun x => Subsingleton.elim x 0⟩

end
