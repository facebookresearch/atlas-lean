/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BettiFunctoriality
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Native bounded-below Betti direct image and adjunction normalization

Both bounded-below functors are the native right-derived functors of the
actual inverse-image and direct-image sheaf functors. The inverse image
is exact. Its ambient comparison is fixed on every actual bounded-below
cochain complex by the native right-derived unit and exact-functor
localization comparison. The derived adjunction unit is fixed by the
termwise ordinary sheaf adjunction and those same native derived units.

Hypercohomology comparison is built from this adjunction, its actual
counit, native constant-pullback isomorphism and canonical shift maps.
It is not an independently supplied cohomology isomorphism.

Source: Kashiwara--Schapira, Sheaves on Manifolds, Section 2.6;
Deligne, Theorie de Hodge II, Section 3; dCHM arXiv:1004.1420v2, Section 1.4.
Native Mathlib derived functors and adjunctions retain their upstream notices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedBettiDirectImages

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open PerverseSheaves BettiRealization BettiFunctoriality ConstructibleComplexes

attribute [local instance] HasDerivedCategory.standard

abbrev RationalPlus (X : TopCat.{0}) := DerivedCategory.Plus (RationalSheaf X)

def unitPlus (X : TopCat.{0}) : RationalPlus X :=
  (DerivedCategory.Plus.singleFunctor (RationalSheaf X) 0).obj (rationalConstantSheaf X)

def unitPlusIso (X : TopCat.{0}) : DerivedCategory.Plus.ι.obj (unitPlus X) ≅ rationalUnit X :=
  (DerivedCategory.Plus.singleFunctorιIso (RationalSheaf X) 0).app (rationalConstantSheaf X)

abbrev inverseImagePlus {X Y : TopCat.{0}} (f : X ⟶ Y) : RationalPlus Y ⥤ RationalPlus X :=
  (pullback ℚ f).rightDerivedFunctorPlus

abbrev directImagePlus {X Y : TopCat.{0}} (f : X ⟶ Y) : RationalPlus X ⥤ RationalPlus Y :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).rightDerivedFunctorPlus

def constantDirectImage {X Y : TopCat.{0}} (f : X ⟶ Y) : RationalDerived Y :=
  DerivedCategory.Plus.ι.obj ((directImagePlus f).obj (unitPlus X))

/-- The ordinary sheaf adjunction unit applied term by term to the actual complex. -/
def ordinaryUnitCochain {X Y : TopCat.{0}} (f : X ⟶ Y)
    (K : CochainComplex.Plus (RationalSheaf Y)) : K ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapCochainComplexPlus.obj
        ((pullback ℚ f).mapCochainComplexPlus.obj K) :=
  ObjectProperty.homMk {
    f := fun i => (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app
      (K.obj.X i)
    comm' := fun i j _ => by
      exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality
        (K.obj.d i j)).symm }

structure ExactInverseImageComparison {X Y : TopCat.{0}} (f : X ⟶ Y) where
  iso : inverseImagePlus f ⋙ DerivedCategory.Plus.ι ≅
    DerivedCategory.Plus.ι ⋙ derivedPullback ℚ f
  shift : NatTrans.CommShift iso.hom ℤ
  cochains : ∀ K : CochainComplex.Plus (RationalSheaf Y),
    DerivedCategory.Plus.ι.map ((pullback ℚ f).rightDerivedFunctorPlusUnit.app K) ≫
      iso.hom.app (DerivedCategory.Plus.Q.obj K) =
    (DerivedCategory.Plus.QCompιIso (RationalSheaf X)).hom.app
      ((pullback ℚ f).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Q.map ((pullback ℚ f).mapCochainComplexPlusCompι.hom.app K) ≫
      (pullback ℚ f).mapDerivedCategoryFactors.inv.app K.obj ≫
      (derivedPullback ℚ f).map ((DerivedCategory.Plus.QCompιIso (RationalSheaf Y)).inv.app K)

/-- A derived adjunction normalized on all native cochains and derived units. -/
structure BoundedDerivedAdjunction {X Y : TopCat.{0}} (f : X ⟶ Y) where
  exactInverse : ExactInverseImageComparison f
  adjunction : inverseImagePlus f ⊣ directImagePlus f
  linear : (inverseImagePlus f).Linear ℚ
  cochain_unit : ∀ K : CochainComplex.Plus (RationalSheaf Y),
    adjunction.unit.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map (ordinaryUnitCochain f K) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).rightDerivedFunctorPlusUnit.app
        ((pullback ℚ f).mapCochainComplexPlus.obj K) ≫
      (directImagePlus f).map ((pullback ℚ f).rightDerivedFunctorPlusUnit.app K)

/-- The native constant-inverse-image isomorphism transported through the faithful inclusion. -/
def inverseImageUnitIso {X Y : TopCat.{0}} {f : X ⟶ Y} (A : BoundedDerivedAdjunction f) :
    (inverseImagePlus f).obj (unitPlus Y) ≅ unitPlus X :=
  DerivedCategory.Plus.ι.preimageIso
    (A.exactInverse.iso.app (unitPlus Y) ≪≫
      (derivedPullback ℚ f).mapIso (unitPlusIso Y) ≪≫ unitInverseImageIso f ≪≫
      (unitPlusIso X).symm)

/-- Actual derived Hom from the rational coefficient unit. -/
abbrev Hypercohomology (Y : TopCat.{0}) (K : RationalDerived Y) (d : ℤ) :=
  rationalUnit Y ⟶ K⟦d⟧

/-- The canonical linear lift of a morphism into the native full bounded-below subcategory. -/
def includedHomLinearMap {Y : TopCat.{0}} (K L : RationalPlus Y) :
    (DerivedCategory.Plus.ι.obj K ⟶ DerivedCategory.Plus.ι.obj L) →ₗ[ℚ] (K ⟶ L) where
  toFun := ObjectProperty.homMk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def compareHom {X Y : TopCat.{0}} {f : X ⟶ Y} (A : BoundedDerivedAdjunction f) (d : ℤ)
    (a : Hypercohomology Y (constantDirectImage f) d) : Cohomology X d :=
  let b := includedHomLinearMap (unitPlus Y) (((directImagePlus f).obj (unitPlus X))⟦d⟧)
    ((unitPlusIso Y).hom ≫ a ≫
      (DerivedCategory.Plus.ι.commShiftIso d).inv.app ((directImagePlus f).obj (unitPlus X)))
  let c := (inverseImageUnitIso A).inv ≫
    (inverseImagePlus f).map (b ≫ ((directImagePlus f).commShiftIso d).inv.app (unitPlus X)) ≫
      A.adjunction.counit.app ((unitPlus X)⟦d⟧)
  (unitPlusIso X).inv ≫ DerivedCategory.Plus.ι.map c ≫
    (DerivedCategory.Plus.ι.commShiftIso d).hom.app (unitPlus X) ≫
      (shiftFunctor (RationalDerived X) d).map (unitPlusIso X).hom

/-- The actual adjunction-induced map from direct-image hypercohomology to source cohomology. -/
def cohomologyComparison {X Y : TopCat.{0}} {f : X ⟶ Y}
    (A : BoundedDerivedAdjunction f) (d : ℤ) :
    Hypercohomology Y (constantDirectImage f) d →ₗ[ℚ] Cohomology X d := by
  letI := A.linear
  exact {
    toFun := compareHom A d
    map_add' := by
      intro a b
      have hAdd {K L : RationalPlus X} (u v : K ⟶ L) :
          (u + v).hom = u.hom + v.hom := rfl
      simp [compareHom, hAdd, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp]
    map_smul' := by
      intro r a
      have hSmul {K L : RationalPlus X} (r : ℚ) (u : K ⟶ L) :
          (r • u).hom = r • u.hom := rfl
      simp [compareHom, hSmul, Functor.map_smul, Linear.comp_smul,
        Linear.smul_comp] }

/-- Postcomposition with the actual shifted map of complexes. -/
def hypercohomologyMap {Y : TopCat.{0}} {K L : RationalDerived Y} (a : K ⟶ L) (d : ℤ) :
    Hypercohomology Y K d →ₗ[ℚ] Hypercohomology Y L d where
  toFun b := b ≫ (shiftFunctor (RationalDerived Y) d).map a
  map_add' b c := by simp [Preadditive.add_comp]
  map_smul' r b := by simp [Linear.smul_comp]

end MathlibExt.AlgebraicGeometry.BoundedBettiDirectImages
