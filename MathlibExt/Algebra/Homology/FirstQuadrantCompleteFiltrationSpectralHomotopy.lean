/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationHomotopy

/-!
# Functorial spectral maps and descent of vertical homotopies

The actual complete horizontal-filtration spectral morphisms preserve identities
and composition. The compatible interval-cone homotopies constructed from a
vertical bicomplex homotopy identify the full spectral morphisms, including
their connecting-map compatibility, after passage to the homotopy category.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

universe v u

namespace HomologicalComplex₂

section Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

/-- A vertical homotopy identifies the actual complete-filtration triangulated
spectral maps, by its compatible homotopies on every interval cone. -/
theorem horizontalCompleteFiltrationTriangulatedSpectralObjectMap_eq_of_homotopy
    {f g : K ⟶ L} (h : _root_.Homotopy (flipMap f) (flipMap g)) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectMap f =
      horizontalCompleteFiltrationTriangulatedSpectralObjectMap g := by
  apply CategoryTheory.Triangulated.SpectralObject.hom_ext
  ext I
  exact HomotopyCategory.eq_of_homotopy _ _
    (horizontalCompleteFiltrationMappingConeHomotopy h I)

/-- The actual complete horizontal filtration as a functor to triangulated
spectral objects. -/
def horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      CategoryTheory.Triangulated.SpectralObject
        (HomotopyCategory C (ComplexShape.up ℤ)) EInt where
  obj := horizontalCompleteFiltrationTriangulatedSpectralObject
  map := horizontalCompleteFiltrationTriangulatedSpectralObjectMap
  map_id K := by
    apply CategoryTheory.Triangulated.SpectralObject.hom_ext
    ext I
    change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((horizontalCompleteFiltrationMappingConeNatTrans (𝟙 K)).app I) = 𝟙 _
    rw [horizontalCompleteFiltrationMappingConeNatTrans_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply CategoryTheory.Triangulated.SpectralObject.hom_ext
    ext I
    change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((horizontalCompleteFiltrationMappingConeNatTrans (f ≫ g)).app I) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((horizontalCompleteFiltrationMappingConeNatTrans f).app I) ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((horizontalCompleteFiltrationMappingConeNatTrans g).app I)
    rw [horizontalCompleteFiltrationMappingConeNatTrans_comp, CategoryTheory.Functor.map_comp]

/-- The functor retains the original complete-filtration triangulated object. -/
@[simp]
theorem horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor.obj K =
      horizontalCompleteFiltrationTriangulatedSpectralObject K := rfl

/-- The functor retains the original actual triangulated spectral map. -/
@[simp]
theorem horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor_map (f : K ⟶ L) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor.map f =
      horizontalCompleteFiltrationTriangulatedSpectralObjectMap f := rfl

end Triangulated

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

/-- A vertical bicomplex homotopy gives equality of the full actual abelian
spectral morphisms at every degree and interval. -/
theorem horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
    {f g : K ⟶ L} (h : _root_.Homotopy (flipMap f) (flipMap g)) :
    horizontalCompleteFiltrationSpectralObjectMap f =
      horizontalCompleteFiltrationSpectralObjectMap g := by
  unfold horizontalCompleteFiltrationSpectralObjectMap
  rw [horizontalCompleteFiltrationTriangulatedSpectralObjectMap_eq_of_homotopy h]

/-- The actual complete horizontal filtration as an abelian spectral-object
functor, with its original interval groups and connecting maps retained. -/
def horizontalCompleteFiltrationSpectralObjectFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      CategoryTheory.Abelian.SpectralObject C EInt where
  obj := horizontalCompleteFiltrationSpectralObject
  map := horizontalCompleteFiltrationSpectralObjectMap
  map_id K := by
    unfold horizontalCompleteFiltrationSpectralObjectMap
    rw [← horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor_map]
    rw [CategoryTheory.Functor.map_id]
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    unfold horizontalCompleteFiltrationSpectralObjectMap
    rw [← horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor_map,
      CategoryTheory.Functor.map_comp]
    exact CategoryTheory.Functor.map_comp _ _ _

/-- The abelian functor retains the exact original complete-filtration object. -/
@[simp]
theorem horizontalCompleteFiltrationSpectralObjectFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationSpectralObjectFunctor.obj K =
      horizontalCompleteFiltrationSpectralObject K := rfl

/-- The abelian functor retains the exact original complete-filtration map. -/
@[simp]
theorem horizontalCompleteFiltrationSpectralObjectFunctor_map (f : K ⟶ L) :
    horizontalCompleteFiltrationSpectralObjectFunctor.map f =
      horizontalCompleteFiltrationSpectralObjectMap f := rfl

end Abelian

end HomologicalComplex₂

end
