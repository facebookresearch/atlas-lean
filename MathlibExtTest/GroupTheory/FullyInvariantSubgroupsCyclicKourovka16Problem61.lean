/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FullyInvariantSubgroupsCyclicKourovka16Problem61

namespace MathlibExt.GroupTheory.FullyInvariantSubgroupsCyclicKourovka16Problem61Wanted

/-- Extract a finite noncyclic witness, with full invariance expressed elementwise. -/
example : ∃ (G : Type) (_ : Group G), Finite G ∧ ¬ IsCyclic G ∧
    ∀ d : ℕ, d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d ∧
      ∀ (φ : G →* G) (x : G), x ∈ H → φ x ∈ H := by
  by_contra h
  apply fullyInvariantSubgroupsOfEachOrderCyclic_refuted
  intro G _ _ hG
  by_contra hcyc
  refine h ⟨G, inferInstance, inferInstance, hcyc, fun d hd ↦ ?_⟩
  obtain ⟨H, hcard, hinv⟩ := hG d hd
  exact ⟨H, hcard, fun φ x hx ↦ hinv φ ⟨x, hx, rfl⟩⟩

end MathlibExt.GroupTheory.FullyInvariantSubgroupsCyclicKourovka16Problem61Wanted
