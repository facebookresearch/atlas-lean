/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient.InvariantAffineOpen

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

-- `exactSource` consumer with the original binders.
example {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W :=
  Scheme.exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation s t hequiv hU hx
-- Higher-universe consumer.
example {X R : Scheme.{max u v}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{max u v},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W :=
  Scheme.exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation s t hequiv hU hx
