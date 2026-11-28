/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.HodgeTate.Representation

/-!
# Tests for Hodge–Tate representations

The trivial representation and `ℚ_p(1)` are Hodge–Tate, `ℚ_p(1)` has the Hodge–Tate numbers
`h₁ = 1`, `h₀ = 0` and `h₋₁ = 0`, `dim_K D_HT(V) ≤ dim V`, and Tate twists compose.
-/

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplex
  Representation
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-! ### Hodge–Tate representations -/

/-- `dim_K D_HT(V) ≤ dim_{ℚ_p} V`, and `V` is Hodge–Tate exactly when the comparison map is an
isomorphism. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (ρ : Representation ℚ_[p] (Galois p) V) [FiniteDimensional ℚ_[p] V] :
    Module.finrank (fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup)
        (ρ.periods (hodgeTateAction p) K.fixingSubgroup) ≤ Module.finrank ℚ_[p] V ∧
      (ρ.IsHodgeTate K ↔
        Function.Bijective (ρ.comparison (hodgeTateAction p) K.fixingSubgroup)) :=
  ⟨finrank_periods_hodgeTateAction_le K ρ, isHodgeTate_iff_comparison_bijective K ρ⟩

/-- The trivial representation on a finite-dimensional `V` is Hodge–Tate: the vectors `1 ⊗ vᵢ`
form a basis of invariants. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] V] : (trivial ℚ_[p] (Galois p) V).IsHodgeTate K :=
  (isHodgeTate_iff_hasFixedBasis K _).2
    ⟨_, Algebra.TensorProduct.basis _ (Module.finBasis ℚ_[p] V), fun i σ _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

/-- `ℚ_p(1)` is Hodge–Tate, with `h₁ = 1`, `h₀ = 0` and `h₋₁ = 0`: its Hodge–Tate weight in the
opposite convention is `-1`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    (cyclotomic p).IsHodgeTate K ∧ (cyclotomic p).hodgeTateNumber K 1 = 1 ∧
      (cyclotomic p).hodgeTateNumber K 0 = 0 ∧ (cyclotomic p).hodgeTateNumber K (-1) = 0 := by
  refine ⟨isHodgeTate_cyclotomic K, ?_, ?_, ?_⟩ <;> simp [hodgeTateNumber_cyclotomic]

/-- `σ` acts on `ℚ_p(1)` by `χ(σ)`, and `ℚ_p(1)(-1)` is the trivial representation. -/
example (σ : Galois p) :
    cyclotomic p σ 1 = cyclotomicScalar p σ ∧
      (cyclotomic p).tateTwist (-1) = trivial ℚ_[p] (Galois p) ℚ_[p] := by
  refine ⟨by simp, ?_⟩
  rw [cyclotomic, tateTwist_tateTwist, add_neg_cancel, tateTwist_zero]

/-- Tate twists compose: `V(1)(-1) = V`. -/
example (ρ : Representation ℚ_[p] (Galois p) V) : (ρ.tateTwist 1).tateTwist (-1) = ρ := by
  rw [tateTwist_tateTwist, add_neg_cancel, tateTwist_zero]
