/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.TameCharacter

@[expose] public section

namespace ValuationSubringTameCharacterTest

/-- Consumer with the original binders: on inertia the tame character only depends on `π` up to
units. -/
public theorem exactSource
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π π' : AlgebraicClosure ℚ) (hπ : π ≠ 0)
    (hπ' : π' ≠ 0) (hu : π' / π ∈ P) (hu' : π / π' ∈ P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ :=
  P.tameCharacter_eq_of_div_mem_of_div_mem π π' hπ hπ' hu hu' hσ

/-- Consumer with the original binders of the unit lemma. -/
public theorem exactSourceUnits
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
      ∃ a : (↥A)ˣ, ((a : ↥A) : AlgebraicClosure ℚ) * z = σ z ∧
        IsLocalRing.residue (↥A) (a : ↥A) = A.tameCharacter z σ) ∧
    ∀ u : (↥A)ˣ, A.tameCharacter ((u : ↥A) : AlgebraicClosure ℚ) σ = 1 :=
  A.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn hσ

/-- The identity automorphism has trivial tame character at every nonzero `π`. -/
public example (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (hπ : π ≠ 0) : P.tameCharacter π 1 = 1 := by
  have h : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π ∈ P := by
    rw [AlgEquiv.one_apply, div_self hπ]
    exact P.one_mem
  rw [P.tameCharacter_of_mem π 1 h]
  have h1 : (⟨(1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π, h⟩ : ↥P) = 1 :=
    Subtype.ext (by simp [hπ])
  rw [h1, map_one]

/-- Boundary: outside `P` the defining ratio gives no information and the value is `0`, so the
inertia hypothesis in the lemmas above is what makes the character meaningful. -/
public example (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : σ π / π ∉ P) :
    P.tameCharacter π σ = 0 := by
  unfold ValuationSubring.tameCharacter
  simp [h]

end ValuationSubringTameCharacterTest
