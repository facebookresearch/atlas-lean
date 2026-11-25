/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Quillen equivalences from actual categorical equivalences

The original unit and counit compare every adjunct map. A weak-class comparison
for the actual forward functor therefore gives the full Hovey criterion.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Equivalence

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]

/-- The actual inverse detects the same entire weak class through the original counit. -/
theorem inverse_map_weakEquivalences_iff (e : C ≌ D)
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      weakEquivalences D (e.functor.map f) ↔ weakEquivalences C f)
    {X Y : D} (f : X ⟶ Y) :
    weakEquivalences C (e.inverse.map f) ↔ weakEquivalences D f := by
  let q : Arrow.mk (e.functor.map (e.inverse.map f)) ≅ Arrow.mk f :=
    Arrow.isoMk (e.counitIso.app X) (e.counitIso.app Y)
      (e.counitIso.hom.naturality f).symm
  exact (hW (e.inverse.map f)).symm.trans ((weakEquivalences D).arrow_mk_iso_iff q)

/-- Every adjunct map is compared by the original counit, without cofibrancy restrictions. -/
theorem homEquiv_weakEquivalences_iff (e : C ≌ D)
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      weakEquivalences D (e.functor.map f) ↔ weakEquivalences C f)
    {X : C} {Y : D} (f : e.functor.obj X ⟶ Y) :
    weakEquivalences D f ↔
      weakEquivalences C (e.toAdjunction.homEquiv X Y f) := by
  have h : e.functor.map (e.toAdjunction.homEquiv X Y f) ≫
      e.counitIso.hom.app Y = f := by
    simpa only [Adjunction.homEquiv_counit, Equivalence.toAdjunction_counit] using
      (e.toAdjunction.homEquiv X Y).symm_apply_apply f
  let q : Arrow.mk (e.functor.map (e.toAdjunction.homEquiv X Y f)) ≅ Arrow.mk f :=
    Arrow.isoMk (Iso.refl (e.functor.obj X)) (e.counitIso.app Y) (by simpa using h.symm)
  exact ((weakEquivalences D).arrow_mk_iso_iff q).symm.trans
    (hW (e.toAdjunction.homEquiv X Y f))

/-- An actual categorical equivalence with the same weak class is a Quillen equivalence. -/
theorem isQuillenEquivalence_of_weakEquivalences (e : C ≌ D)
    [hQ : e.toAdjunction.IsQuillenAdjunction]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      weakEquivalences D (e.functor.map f) ↔ weakEquivalences C f) :
    e.toAdjunction.IsQuillenEquivalence where
  toIsQuillenAdjunction := hQ
  homEquiv_weakEquivalence_iff f := e.homEquiv_weakEquivalences_iff hW f

end CategoryTheory.Equivalence
