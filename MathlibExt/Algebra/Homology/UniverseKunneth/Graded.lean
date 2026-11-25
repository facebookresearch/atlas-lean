/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.UniverseTensorExactness
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyAdapter
public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import Mathlib.Algebra.Homology.SingleHomology
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.Algebra.Homology.GradedHomology.Monoidal

/-!
# Canonical cycle Künneth maps over the original larger-world coefficient ring

The scalar ring is the original `R : Type u`. The coefficient category is
the actual `ModuleCat.{max u v} R` with the fixed UniverseTensor offset v.
The tensorator is literally the native cycle pairing of the identity chain
map, descended to homology and inserted through native graded coproducts.
Its definition does not use a chosen field Künneth inverse or certificate.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.UniverseKunneth

variable {R : Type u} [CommRing R]


/-- The original-field homology functor in the fixed common coefficient world. -/
abbrev homologyFunctor : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) ⥤ (GradedObject ℕ
  (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R)) := gradedHomologyFunctor
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) (ComplexShape.down ℕ)

/-- The canonical bidegree original-field homology pairing. -/
abbrev pair (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q : ℕ) :
    K.homology p ⊗ L.homology q ⟶ (K ⊗ L).homology (p + q) :=
  ChainGradedPairing.pairHomology (𝟙 (K ⊗ L))
    (ChainGradedPairing.homologyDescentData (𝟙 (K ⊗ L))) p q

/-- The actual original-ring canonical cycle tensorator in the actual common world. -/
def tensorator (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :
    homologyFunctor.obj K ⊗ homologyFunctor.obj L ⟶ homologyFunctor.obj (K ⊗ L) :=
  HomologicalComplex.GradedHomology.tensorator K L

@[reassoc (attr := simp)]
theorem ι_tensorator (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q n : ℕ) (h : p
  + q = n) :
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K) (homologyFunctor.obj L)
      p q n h ≫ tensorator K L n =
      pair K L p q ≫ (homologyIsoOfEq (K ⊗ L) h).hom :=
  HomologicalComplex.GradedHomology.ι_tensorator K L p q n h

/-- Actual bidegree cycle pairings are natural under both original chain maps. -/
@[reassoc]
theorem pair_naturality {K L K' L' : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)} (f : K ⟶
  K') (g : L ⟶ L') (p q : ℕ) :
    (homologyMap f p ⊗ₘ homologyMap g q) ≫ pair K' L' p q =
      pair K L p q ≫ homologyMap (f ⊗ₘ g) (p + q) := by
  exact HomologicalComplex.GradedHomology.pair_naturality f g p q


/-- The actual original-ring tensorator is natural in both complex variables. -/
@[reassoc]
theorem tensorator_naturality {K L K' L' : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)} (f
  : K ⟶ K') (g : L ⟶ L') :
    (homologyFunctor.map f ⊗ₘ homologyFunctor.map g) ≫ tensorator K' L' =
      tensorator K L ≫ homologyFunctor.map (f ⊗ₘ g) := by
  exact HomologicalComplex.GradedHomology.tensorator_naturality f g


/-- The actual lifted-unit homology comparison over the original ring. -/
def unitIso : 𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R)) ≅ homologyFunctor.obj (𝟙_
  (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitIso (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

/-- The actual original-field map into homology of the fixed chain unit. -/
def unitMap : 𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R)) ⟶ homologyFunctor.obj (𝟙_
  (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitMap (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

@[simp]
theorem unitMap_zero : unitMap.{u,v} (R := R) 0 =
    (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))).hom ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.UniverseScalarRestriction.Modules.{u,v}
        R))).inv := by
  exact HomologicalComplex.GradedHomology.unitMap_zero (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

instance unitMap_isIso : IsIso (unitMap.{u,v} (R := R)) := by
  exact HomologicalComplex.GradedHomology.unitMap_isIso (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))

end HomologicalComplex.UniverseKunneth
