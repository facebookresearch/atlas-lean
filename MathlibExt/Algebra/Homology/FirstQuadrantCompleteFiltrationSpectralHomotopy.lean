/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationHomotopy

/-!
# Vertical homotopies and functorial complete-filtration spectral objects

Let C be a preadditive category with a zero object and finite coproducts,
and let K be a bicomplex with both differentials lowering nonnegative
degrees. Its complete horizontal filtration is indexed by
EInt = ℤ ∪ {−∞,+∞}; a finite stage a ≥ 0 contains columns p ≤ a,
negative and bottom stages are zero, and the top stage is Tot(K).

Reindex the filtered chain complexes as integer cochain complexes,
with chain degree n placed in cochain degree −n. Their interval
mapping cones give a triangulated spectral object in the homotopy
category. Bicomplex maps act functorially on this object.

If f,g : K → L are chain homotopic after interchanging the bicomplex
coordinates, their full triangulated spectral maps are equal.
Thus vertical bicomplex homotopies preserve all interval maps and
connecting maps. When C is abelian, applying cochain homology gives
the corresponding abelian spectral-object functor and the same
equality of its morphisms. The object and morphism worlds are independent.
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

/-- Let C be preadditive with a zero object and finite
coproducts, and let K,L be nonnegative homological bicomplexes.
If f,g : K → L admit a chain homotopy after flipping the two
bicomplex coordinates, their induced maps of complete-filtration
triangulated spectral objects are equal.
The equality includes every interval cone and connecting map. -/
theorem horizontalCompleteFiltrationTriangulatedSpectralObjectMap_eq_of_homotopy
    {f g : K ⟶ L} (h : _root_.Homotopy (flipMap f) (flipMap g)) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectMap f =
      horizontalCompleteFiltrationTriangulatedSpectralObjectMap g := by
  apply CategoryTheory.Triangulated.SpectralObject.hom_ext
  ext I
  exact HomotopyCategory.eq_of_homotopy _ _
    (horizontalCompleteFiltrationMappingConeHomotopy h I)

/-- For a preadditive category C with a zero object and finite
coproducts, complete horizontal filtration defines a functor from
nonnegative homological bicomplexes to triangulated spectral objects
indexed by EInt in HomotopyCategory(C,up ℤ).
Its interval values are the cones of the reindexed filtration maps,
and bicomplex maps induce the interval-cone morphisms. -/
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

/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, the complete
triangulated filtration functor has object value the spectral object
of the cones F_a(K) → F_b(K), a ≤ b in EInt, after reindexing
chain degree n as cochain degree −n. -/
@[simp]
theorem horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor.obj K =
      horizontalCompleteFiltrationTriangulatedSpectralObject K := rfl

/-- For a map f : K → L of nonnegative homological bicomplexes
in a preadditive category with a zero object and finite coproducts,
the triangulated filtration functor sends f to its complete
filtration spectral map. On each interval it is the induced
mapping-cone morphism in the homotopy category. -/
@[simp]
theorem horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor_map (f : K ⟶ L) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectFunctor.map f =
      horizontalCompleteFiltrationTriangulatedSpectralObjectMap f := rfl

end Triangulated

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

/-- For nonnegative homological bicomplexes K,L in an abelian
category C, if f,g : K → L are chain homotopic after flipping the
bicomplex coordinates, their complete horizontal-filtration
abelian spectral maps are equal in every degree and interval,
including compatibility with connecting morphisms. -/
theorem horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
    {f g : K ⟶ L} (h : _root_.Homotopy (flipMap f) (flipMap g)) :
    horizontalCompleteFiltrationSpectralObjectMap f =
      horizontalCompleteFiltrationSpectralObjectMap g := by
  unfold horizontalCompleteFiltrationSpectralObjectMap
  rw [horizontalCompleteFiltrationTriangulatedSpectralObjectMap_eq_of_homotopy h]

/-- For an abelian category C, complete horizontal filtration
defines a functor from nonnegative homological bicomplexes to
abelian spectral objects in C indexed by EInt.
It applies the cochain homology functor to the triangulated
interval-cone spectral object and its connecting maps. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category C, the complete abelian filtration functor has object
value the spectral object of the relative homology of its
reindexed interval cones. This is the complete horizontal
filtration spectral object of K. -/
@[simp]
theorem horizontalCompleteFiltrationSpectralObjectFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationSpectralObjectFunctor.obj K =
      horizontalCompleteFiltrationSpectralObject K := rfl

/-- For a map f : K → L of nonnegative homological bicomplexes
in an abelian category C, the complete abelian filtration functor
sends f to the homology maps of its interval-cone morphisms.
These are the complete-filtration spectral maps, with their
connecting-morphism compatibility. -/
@[simp]
theorem horizontalCompleteFiltrationSpectralObjectFunctor_map (f : K ⟶ L) :
    horizontalCompleteFiltrationSpectralObjectFunctor.map f =
      horizontalCompleteFiltrationSpectralObjectMap f := rfl

end Abelian

end HomologicalComplex₂

end
