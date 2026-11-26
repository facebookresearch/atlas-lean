/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonIdealExistsMemVanDerWaerdenLacunaryDFinNotMemSidonIdeal

namespace MathlibExtTest.Combinatorics.Additive.SidonIdealExistsMemVanDerWaerdenLacunaryDFinNotMemSidonIdeal

open MetaMathlibExt

theorem exists_not_isSidon :
    ∃ A : Set ℕ, A ∈ vanDerWaerdenIdeal ∧ A ∈ generatedIdeal IsGapLacunarySet ∧
      A ∈ dFinIdeal ∧ ¬ A.IsSidon := by
  obtain ⟨A, hW, hL, hD, hSi⟩ := exists_mem_vanDerWaerden_lacunary_dFin_not_mem_sidonIdeal
  exact ⟨A, hW, hL, hD, fun h => hSi (mem_generatedIdeal h)⟩

theorem exists_no_finite_sidon_cover :
    ∃ A : Set ℕ, A ∈ vanDerWaerdenIdeal ∧ A ∈ generatedIdeal IsGapLacunarySet ∧
      A ∈ dFinIdeal ∧ ∀ (n : ℕ) (S : Fin n → Set ℕ),
        (∀ j, (S j).IsSidon) → ∃ x ∈ A, ∀ j, x ∉ S j := by
  classical
  obtain ⟨A, hW, hL, hD, hSi⟩ := exists_mem_vanDerWaerden_lacunary_dFin_not_mem_sidonIdeal
  refine ⟨A, hW, hL, hD, ?_⟩
  intro n S hS
  by_contra! h
  apply hSi
  refine ⟨n, S, hS, ?_⟩
  intro x hx
  exact Set.mem_iUnion.mpr (h x hx)

#print axioms exists_not_isSidon
#print axioms exists_no_finite_sidon_cover

end MathlibExtTest.Combinatorics.Additive.SidonIdealExistsMemVanDerWaerdenLacunaryDFinNotMemSidonIdeal
