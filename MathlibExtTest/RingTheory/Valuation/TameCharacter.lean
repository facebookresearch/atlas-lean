/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.TameCharacter
import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section

namespace ValuationSubringTameCharacterTest

/-- Consumer with the original binders: on inertia the tame character only depends on `π` up to
units. -/
private theorem exactSource
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π π' : AlgebraicClosure ℚ) (hπ : π ≠ 0)
    (hπ' : π' ≠ 0) (hu : π' / π ∈ P) (hu' : π / π' ∈ P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ :=
  P.tameCharacter_eq_of_div_mem_of_div_mem π π' hπ hπ' hu hu' hσ

/-- Consumer with the original binders of the unit lemma. -/
private theorem exactSourceUnits
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
      ∃ a : (↥A)ˣ, ((a : ↥A) : AlgebraicClosure ℚ) * z = σ z ∧
        IsLocalRing.residue (↥A) (a : ↥A) = A.tameCharacter z σ) ∧
    ∀ u : (↥A)ˣ, A.tameCharacter ((u : ↥A) : AlgebraicClosure ℚ) σ = 1 :=
  A.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn hσ

/-- The identity automorphism has trivial tame character at every nonzero `π`. -/
example (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (hπ : π ≠ 0) : P.tameCharacter π (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 := by
  have h : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π ∈ P := by
    rw [AlgEquiv.one_apply, div_self hπ]
    exact P.one_mem
  rw [P.tameCharacter_of_mem π 1 h]
  have h1 : (⟨(1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π, h⟩ : ↥P) = 1 :=
    Subtype.ext (by simp [hπ])
  rw [h1, map_one]

/-- Boundary: outside `P` the defining ratio gives no information and the value is `0`, so the
inertia hypothesis in the lemmas above is what makes the character meaningful. -/
example (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : σ π / π ∉ P) :
    P.tameCharacter π σ = 0 := by
  unfold ValuationSubring.tameCharacter
  simp [h]

/-- The invariance lemma over an arbitrary algebraic extension `L / K`. -/
private theorem generalExtension {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (P : ValuationSubring L) (π π' : L) (hπ : π ≠ 0) (hπ' : π' ≠ 0)
    (hu : π' / π ∈ P) (hu' : π / π' ∈ P) {σ : L ≃ₐ[K] L} (hσ : σ ∈ P.inertiaSubgroupIn K) :
    P.tameCharacter π' σ = P.tameCharacter π σ :=
  P.tameCharacter_eq_of_div_mem_of_div_mem π π' hπ hπ' hu hu' hσ

/-- A concrete value outside `AlgebraicClosure ℚ`: for complex conjugation over `ℝ`, `π = 1 + i`
and `P = ⊤`, the tame character is the residue of `conj (1 + i) / (1 + i) = -i`. The inverse
ratio `(1 + i) / conj (1 + i)` is `i`, so this pins the direction of the ratio. -/
example : (⊤ : ValuationSubring ℂ).tameCharacter (1 + Complex.I) Complex.conjAe =
    IsLocalRing.residue _ ⟨-Complex.I, ValuationSubring.mem_top _⟩ := by
  have h0 : (1 + Complex.I : ℂ) ≠ 0 := fun h => by simpa using congrArg Complex.re h
  have hval : Complex.conjAe (1 + Complex.I) / (1 + Complex.I) = -Complex.I := by
    rw [div_eq_iff h0, Complex.conjAe_coe, map_add, map_one, Complex.conj_I]
    linear_combination Complex.I_sq
  rw [ValuationSubring.tameCharacter_of_mem _ _ _ (ValuationSubring.mem_top _)]
  exact congrArg _ (Subtype.ext hval)

end ValuationSubringTameCharacterTest
