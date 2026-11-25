/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceNaturalComparison

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory HomotopicalAlgebra
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L M : C ⥤ D} {R S : D ⥤ C}

example (a : L ⊣ R) (e : L ≅ M) [a.IsQuillenEquivalence] :
    (a.ofNatIsoLeft e).IsQuillenEquivalence := inferInstance

example (a : L ⊣ R) (e : R ≅ S) [a.IsQuillenEquivalence] :
    (a.ofNatIsoRight e).IsQuillenEquivalence := inferInstance

example (a : L ⊣ R) (b : M ⊣ R) (e : L ≅ M)
    (hUnit : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) = b.unit.app X)
    (X : C) (Y : D) (f : M.obj X ⟶ Y) :
    b.homEquiv X Y f = a.homEquiv X Y (e.hom.app X ≫ f) :=
  Adjunction.homEquiv_of_leftComparison a b e hUnit X Y f

example (a : L ⊣ R) (b : M ⊣ R) (e : L ≅ M)
    (hUnit : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) = b.unit.app X)
    (X : C) (Y : D) (f : X ⟶ R.obj Y) :
    (b.homEquiv X Y).symm f = e.inv.app X ≫ (a.homEquiv X Y).symm f :=
  Adjunction.homEquiv_symm_of_leftComparison a b e hUnit X Y f

example (a : L ⊣ R) (b : M ⊣ R) (e : L ≅ M)
    (hUnit : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) = b.unit.app X)
    [a.IsQuillenEquivalence]
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : M.obj X ⟶ Y) :
    weakEquivalences D f ↔ weakEquivalences C (b.homEquiv X Y f) := by
  let _ : b.IsQuillenEquivalence := Adjunction.IsQuillenEquivalence.of_leftComparison a b e hUnit
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff (adj := b) f
