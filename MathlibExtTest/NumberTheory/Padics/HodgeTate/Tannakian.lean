/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.HodgeTate.Tannakian

/-!
# Tests for the Tannakian properties of Hodge–Tate representations

`ℚ_p(1) ⊗ ℚ_p(1)` is Hodge–Tate with a one-dimensional `D_HT`; the dual of `ℚ_p(1)`,
`ℚ_p(1)* ⊗ ℚ_p(1)` and `ℚ_p(1) × ℚ_p(1)` with its subrepresentations and quotients are Hodge–Tate;
the factors of a Hodge–Tate direct sum are Hodge–Tate; and on Hodge–Tate representations `D_HT` is
exact and faithful, and Fontaine's maps for tensor products and duals are isomorphisms.
-/

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplex
  Representation
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℚ_[p] V₁]
  [AddCommGroup V₂] [Module ℚ_[p] V₂]

/-! ### `ℚ_p(1)` -/

/-- `ℚ_p(1) ⊗ ℚ_p(1)` is Hodge–Tate, and `D_HT(ℚ_p(1) ⊗ ℚ_p(1))` is one-dimensional over
`B_HT^{G_K} = K`. -/
example : ((cyclotomic p).tprod (cyclotomic p)).IsHodgeTate K ∧
    Module.finrank (fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup)
      (((cyclotomic p).tprod (cyclotomic p)).periods (hodgeTateAction p) K.fixingSubgroup) =
      1 := by
  have h := (isHodgeTate_cyclotomic K).tprod (isHodgeTate_cyclotomic K)
  refine ⟨h, h.2.trans ?_⟩
  rw [Module.finrank_tensorProduct, Module.finrank_self, mul_one]

/-- The dual of `ℚ_p(1)` is Hodge–Tate, and Fontaine's map `D_HT(ℚ_p(1)*) → D_HT(ℚ_p(1))*` is
bijective. -/
example : (cyclotomic p).dual.IsHodgeTate K ∧
    Function.Bijective ((cyclotomic p).periodsDual (hodgeTateAction p) K.fixingSubgroup) :=
  ⟨(isHodgeTate_cyclotomic K).dual, (isHodgeTate_cyclotomic K).periodsDual_bijective⟩

/-- `ℚ_p(1)* ⊗ ℚ_p(1)` is Hodge–Tate, and Fontaine's map
`D_HT(ℚ_p(1)*) ⊗ D_HT(ℚ_p(1)) → D_HT(ℚ_p(1)* ⊗ ℚ_p(1))` is bijective. -/
example : ((cyclotomic p).dual.tprod (cyclotomic p)).IsHodgeTate K ∧
    Function.Bijective
      (periodsTensor (cyclotomic p).dual (cyclotomic p) (hodgeTateAction p) K.fixingSubgroup) :=
  ⟨(isHodgeTate_cyclotomic K).dual.tprod (isHodgeTate_cyclotomic K),
    (isHodgeTate_cyclotomic K).dual.periodsTensor_bijective (isHodgeTate_cyclotomic K)⟩

/-- `ℚ_p(1) × ℚ_p(1)` is Hodge–Tate, and so are its subrepresentations and its quotients. -/
example (W : Subrepresentation ((cyclotomic p).prod (cyclotomic p))) :
    ((cyclotomic p).prod (cyclotomic p)).IsHodgeTate K ∧ W.toRepresentation.IsHodgeTate K ∧
      W.quotient.IsHodgeTate K := by
  have h := (isHodgeTate_cyclotomic K).prod (isHodgeTate_cyclotomic K)
  exact ⟨h, h.subrepresentation W, h.quotient W⟩

/-! ### Hodge–Tate representations in general -/

/-- The factors of a Hodge–Tate direct sum are Hodge–Tate: by `isHodgeTate_prod_iff`, or through
the injective inclusion of the first factor and the surjective projection onto the second. -/
example (ρ₁ : Representation ℚ_[p] (Galois p) V₁) (ρ₂ : Representation ℚ_[p] (Galois p) V₂)
    (h : (ρ₁.prod ρ₂).IsHodgeTate K) :
    (ρ₁.IsHodgeTate K ∧ ρ₂.IsHodgeTate K) ∧ ρ₁.IsHodgeTate K ∧ ρ₂.IsHodgeTate K :=
  ⟨isHodgeTate_prod_iff.1 h,
    h.of_injective (f := IntertwiningMap.inl ℚ_[p] ρ₁ ρ₂) LinearMap.inl_injective,
    h.of_surjective (IntertwiningMap.snd_surjective ρ₁ ρ₂)⟩

/-- `D_HT` maps `0 → W → V → V ⧸ W → 0` to a short exact sequence, for a subrepresentation `W` of
a Hodge–Tate representation `V`. -/
example (ρ : Representation ℚ_[p] (Galois p) V₁) (h : ρ.IsHodgeTate K)
    (W : Subrepresentation ρ) :
    Function.Injective (periodsMap (hodgeTateAction p) K.fixingSubgroup W.subtype) ∧
      Function.Exact (periodsMap (hodgeTateAction p) K.fixingSubgroup W.subtype)
        (periodsMap (hodgeTateAction p) K.fixingSubgroup W.mkQ) ∧
      Function.Surjective (periodsMap (hodgeTateAction p) K.fixingSubgroup W.mkQ) :=
  h.shortExact_periodsMap W.subtype_injective W.mkQ_surjective W.exact_subtype_mkQ

/-- `D_HT` maps the exact sequence `V₁ → V₁ × V₂ → V₂` to an exact sequence when `V₁` is
Hodge–Tate. -/
example (ρ₁ : Representation ℚ_[p] (Galois p) V₁) (ρ₂ : Representation ℚ_[p] (Galois p) V₂)
    (h₁ : ρ₁.IsHodgeTate K) :
    Function.Exact
      (periodsMap (hodgeTateAction p) K.fixingSubgroup (IntertwiningMap.inl ℚ_[p] ρ₁ ρ₂))
      (periodsMap (hodgeTateAction p) K.fixingSubgroup (IntertwiningMap.snd ℚ_[p] ρ₁ ρ₂)) :=
  h₁.exact_periodsMap fun x => ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨_, hy⟩ => hy ▸ rfl⟩

/-- `D_HT` is faithful on Hodge–Tate representations. -/
example (ρ₁ : Representation ℚ_[p] (Galois p) V₁) (ρ₂ : Representation ℚ_[p] (Galois p) V₂)
    (h₁ : ρ₁.IsHodgeTate K) (f f' : ρ₁.IntertwiningMap ρ₂)
    (hf : periodsMap (hodgeTateAction p) K.fixingSubgroup f =
      periodsMap (hodgeTateAction p) K.fixingSubgroup f') : f = f' :=
  h₁.eq_of_periodsMap_eq hf

/-- The isomorphisms `D_HT(V₁) ⊗ D_HT(V₂) ≃ D_HT(V₁ ⊗ V₂)` and `D_HT(V₁*) ≃ D_HT(V₁)*` are
Fontaine's natural maps: the first sends `x ⊗ y` to the product of `x` and `y`. -/
example (ρ₁ : Representation ℚ_[p] (Galois p) V₁) (ρ₂ : Representation ℚ_[p] (Galois p) V₂)
    (h₁ : ρ₁.IsHodgeTate K) (h₂ : ρ₂.IsHodgeTate K)
    (x : ρ₁.periods (hodgeTateAction p) K.fixingSubgroup)
    (y : ρ₂.periods (hodgeTateAction p) K.fixingSubgroup)
    (z : ρ₁.dual.periods (hodgeTateAction p) K.fixingSubgroup) :
    (h₁.periodsTensorEquiv h₂ (x ⊗ₜ y) : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] (V₁ ⊗[ℚ_[p]] V₂)) =
        tensorMul ℚ_[p] ℂ_[p][T;T⁻¹] V₁ V₂ x y ∧
      h₁.periodsDualEquiv z = ρ₁.periodsDual (hodgeTateAction p) K.fixingSubgroup z := by
  simp
