/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.HodgeTate.Decomposition

/-!
# Tests for the graded decomposition of `D_HT(V)`

The components of `B_HT ⊗ V` on pure tensors and their `ℂ_p`-linearity, the elementwise
decomposition of `D_HT(V)`, the decomposition as an isomorphism and by the inclusions of the
degrees; `Σᵢ hᵢ ≤ dim V` with equality exactly for Hodge–Tate representations, the sum of the
Hodge–Tate numbers of `ℚ_p(1)` is `1`, and that of the trivial representation on `V` is
`dim V`.
-/

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplex
  Representation
open scoped TensorProduct DirectSum

variable (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- The component of degree `i` of `c tⁱ ⊗ v` is `c ⊗ v`, and its other components vanish. -/
example (i j : ℤ) (c : ℂ_[p]) (v : V) (hij : j ≠ i) :
    hodgeTateComponent p V i ((C c * T i) ⊗ₜ v) = c ⊗ₜ v ∧
      hodgeTateComponent p V j ((C c * T i) ⊗ₜ v) = 0 := by
  rw [hodgeTateComponent_tmul, hodgeTateComponent_tmul, ← single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij,
    TensorProduct.zero_tmul]
  exact ⟨rfl, rfl⟩

/-- The components are `ℂ_p`-linear. -/
example (i : ℤ) (c : ℂ_[p]) (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) :
    hodgeTateComponent p V i (C c • x) = c • hodgeTateComponent p V i x :=
  hodgeTateComponent_C_smul i c x

/-- `x ∈ D_HT(V)` exactly when each component `xᵢ` lies in `(ℂ_p(i) ⊗ V)^{G_K}`, that is,
`χ(σ)ⁱ (σ ⊗ ρ(σ)) xᵢ = xᵢ` for `σ ∈ G_K`. -/
example (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) :
    x ∈ ρ.periods (hodgeTateAction p) K.fixingSubgroup ↔ ∀ i, ∀ σ ∈ K.fixingSubgroup,
      cyclotomicScalar p σ ^ i • TensorProduct.map (completionGalois p σ).toLinearMap (ρ σ)
        (hodgeTateComponent p V i x) = hodgeTateComponent p V i x := by
  simp only [mem_periods_hodgeTateAction_iff, mem_twistPeriods]

/-- The decomposition `D_HT(V) ≃ ⨁ᵢ (ℂ_p(i) ⊗ V)^{G_K}` sends `x` to its components, and is
inverse to the map induced by the inclusions `y ↦ y tⁱ`. -/
example (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ρ.periods (hodgeTateAction p) K.fixingSubgroup) (i : ℤ) :
    (periodsHodgeTateEquiv ρ K x i : ℂ_[p] ⊗[ℚ_[p]] V) = hodgeTateComponent p V i x ∧
      DirectSum.toModule ℚ_[p] ℤ _ (hodgeTateInclusion ρ K) (periodsHodgeTateEquiv ρ K x) = x :=
  ⟨coe_periodsHodgeTateEquiv_apply ρ K x i, (periodsHodgeTateEquiv ρ K).symm_apply_apply x⟩

/-- `Σᵢ hᵢ ≤ dim V`, with equality exactly for Hodge–Tate representations, and then
`dim_K D_HT(V) = Σᵢ hᵢ = dim V`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (ρ : Representation ℚ_[p] (Galois p) V) [FiniteDimensional ℚ_[p] V] :
    ∑ᶠ i, ρ.hodgeTateNumber K i ≤ Module.finrank ℚ_[p] V ∧
      (ρ.IsHodgeTate K ↔ ∑ᶠ i, ρ.hodgeTateNumber K i = Module.finrank ℚ_[p] V) ∧
      (Function.support (ρ.hodgeTateNumber K)).Finite :=
  ⟨finsum_hodgeTateNumber_le K ρ, isHodgeTate_iff_finsum_hodgeTateNumber K ρ,
    finite_support_hodgeTateNumber K ρ⟩

/-- The Hodge–Tate numbers of `ℚ_p(1)` sum to `1 = dim ℚ_p(1)`, so the criterion recovers that
`ℚ_p(1)` is Hodge–Tate. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∑ᶠ i, (cyclotomic p).hodgeTateNumber K i = 1 ∧ (cyclotomic p).IsHodgeTate K := by
  have h : ∑ᶠ i, (cyclotomic p).hodgeTateNumber K i = 1 := by
    rw [finsum_eq_single _ 1 fun i hi => by simp [hodgeTateNumber_cyclotomic, hi]]
    simp [hodgeTateNumber_cyclotomic]
  refine ⟨h, (isHodgeTate_iff_finsum_hodgeTateNumber K _).2 ?_⟩
  rw [h, Module.finrank_self]

/-- The Hodge–Tate numbers of the trivial representation on a finite-dimensional `V` sum to
`dim V`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] V] :
    ∑ᶠ i, (trivial ℚ_[p] (Galois p) V).hodgeTateNumber K i = Module.finrank ℚ_[p] V :=
  (isHodgeTate_iff_finsum_hodgeTateNumber K _).1 ((isHodgeTate_iff_hasFixedBasis K _).2
    ⟨_, Algebra.TensorProduct.basis _ (Module.finBasis ℚ_[p] V), fun i σ _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩)
