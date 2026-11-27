/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.ContinuousH1

open CategoryTheory groupCohomology

universe u

/-- Unfolding: the zero class lies in continuous `H¹`, by the
characterization through level-constant cocycles. -/
example {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G) :
    (0 : H1 M) ∈ continuousH1 r M := by
  rw [mem_continuousH1_iff]
  exact ⟨0, isLevelConstant₁_const r (0 : M), by simp⟩

/-- Nontrivial instance: for the trivial representation of
`Multiplicative ℤ` over `ℚ`, a level-constant cocycle maps into
continuous `H¹`. All hypotheses (`CommRing`, `Group`, the Galois
homomorphism `r`) are instantiated. -/
example :
    let r : Multiplicative ℤ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := 1
    let M : Rep ℚ (Multiplicative ℤ) := Rep.trivial ℚ (Multiplicative ℤ) ℚ
    ∀ c : cocycles₁ M, IsLevelConstant₁ r c → (H1π M).hom c ∈ continuousH1 r M :=
  fun c hc => H1π_mem_continuousH1 _ _ hc

/-- The characterization is available in a higher universe. -/
example {k G : Type (u + 1)} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G)
    (x : H1 M) :
    x ∈ continuousH1 r M ↔ ∃ c : cocycles₁ M, IsLevelConstant₁ r c ∧
      (H1π M).hom c = x :=
  mem_continuousH1_iff r M x
