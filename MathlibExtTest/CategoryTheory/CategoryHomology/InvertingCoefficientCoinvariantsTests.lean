/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryHomology.InvertingCoefficientCoinvariants

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology

universe uJ vJ uA

noncomputable section

#check invertingCoefficientCore
#print axioms invertingCoefficientCore
#check invertingCoefficientExtension
#print axioms invertingCoefficientExtension
#check invertingCoefficientRestrictionIso
#print axioms invertingCoefficientRestrictionIso
#check invertingCoefficientRootAction
#print axioms invertingCoefficientRootAction
#check invertingCoefficientRootAction_cocone_invariant
#print axioms invertingCoefficientRootAction_cocone_invariant
#check invertingCoefficientRootTransport
#print axioms invertingCoefficientRootTransport
#check invertingCoefficientRootTransport_self
#print axioms invertingCoefficientRootTransport_self
#check invertingCoefficientColimitCoinvariantsIso
#print axioms invertingCoefficientColimitCoinvariantsIso
#check invertingCoefficientHomologyZeroCoinvariantsIso
#print axioms invertingCoefficientHomologyZeroCoinvariantsIso
#check invertingCoefficientHomologyZeroCoinvariantsIso_class
#print axioms invertingCoefficientHomologyZeroCoinvariantsIso_class
#check invertingCoefficientCoinvariants_subsingleton_of_homologyZero_isZero
#print axioms invertingCoefficientCoinvariants_subsingleton_of_homologyZero_isZero

namespace InvertingCoefficientCoinvariantsTests

variable {J : Type uJ} [Category.{vJ} J] (M : J ⥤ AddCommGrpCat.{uA})
  [∀ {i j : J} (f : i ⟶ j), IsIso (M.map f)]

example (s : Cocone M) (i : J) (g : End ((SSet.categoryNerveUnit J).obj i)) :
    (s.ι.app i).hom.toIntLinearMap ∘ₗ invertingCoefficientRootAction M i g =
      (s.ι.app i).hom.toIntLinearMap :=
  invertingCoefficientRootAction_cocone_invariant M s i g

variable [(CategoryTheory.nerve J).IsConnected] [HasColimit M]
  [HasCoproducts.{max uJ vJ} AddCommGrpCat.{uA}]

example (i : J) : homologyWithCoefficients M 0 ≅ AddCommGrpCat.of
    (Representation.Coinvariants (invertingCoefficientRootAction M i)) :=
  invertingCoefficientHomologyZeroCoinvariantsIso M i

example (i : J) :
    coefficientHomologyClass M i ≫ (invertingCoefficientHomologyZeroCoinvariantsIso M i).hom =
      AddCommGrpCat.ofHom
        (Representation.Coinvariants.mk (invertingCoefficientRootAction M i)).toAddMonoidHom :=
  invertingCoefficientHomologyZeroCoinvariantsIso_class M i

example (i : J) (h : IsZero (homologyWithCoefficients M 0)) :
    Subsingleton (Representation.Coinvariants (invertingCoefficientRootAction M i)) :=
  invertingCoefficientCoinvariants_subsingleton_of_homologyZero_isZero M i h

end InvertingCoefficientCoinvariantsTests

#check CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap

#check CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap_app
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap_app

#check CategoryTheory.CategoryHomology.invertingCoefficientRootMap
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientRootMap

#check CategoryTheory.CategoryHomology.invertingCoefficientRootMap_apply
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientRootMap_apply

namespace InvertingCoefficientNaturalMapTests

variable {J : Type uJ} [Category.{vJ} J] {M N : J ⥤ AddCommGrpCat.{uA}}
  [∀ {i j : J} (f : i ⟶ j), IsIso (M.map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso (N.map f)]
  (α : M ⟶ N) (i : J)

example :
    (invertingCoefficientExtensionMap M α).app ((SSet.categoryNerveUnit J).obj i) ≫
      ((invertingCoefficientRestrictionIso N).app i).hom =
    ((invertingCoefficientRestrictionIso M).app i).hom ≫ α.app i :=
  invertingCoefficientExtensionMap_app M α i

example (g : End ((SSet.categoryNerveUnit J).obj i)) (v : M.obj i) :
    (α.app i).hom (invertingCoefficientRootAction M i g v) =
      invertingCoefficientRootAction N i g ((α.app i).hom v) :=
  by
    have h := Representation.IntertwiningMap.isIntertwining
      (invertingCoefficientRootAction M i) (invertingCoefficientRootAction N i)
      (invertingCoefficientRootMap M α i) g v
    simpa only [invertingCoefficientRootMap_apply] using h

end InvertingCoefficientNaturalMapTests

#check CategoryTheory.CategoryHomology.invertingCoefficientExtension_edge
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientExtension_edge
#check CategoryTheory.CategoryHomology.invertingCoefficientRootAction_apply
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientRootAction_apply

namespace InvertingCoefficientPublicCharacteristicsTests

open scoped Simplicial

variable {J : Type uJ} [Category.{vJ} J] (M : J ⥤ AddCommGrpCat.{uA})
  [∀ {i j : J} (f : i ⟶ j), IsIso (M.map f)]

example {x y : (CategoryTheory.nerve J) _⦋0⦌} (e : (CategoryTheory.nerve J).Edge x y) :
    (invertingCoefficientExtension M).map (SSet.FundamentalGroupoid.homMk e) ≫
        (invertingCoefficientVertexIso M y).hom =
      (invertingCoefficientVertexIso M x).hom ≫ M.map (CategoryTheory.nerve.homEquiv e) :=
  invertingCoefficientExtension_edge M e

example (i : J) (g : End ((SSet.categoryNerveUnit J).obj i)) (v : M.obj i) :
    invertingCoefficientRootAction M i g v =
      (((invertingCoefficientRestrictionIso M).app i).inv ≫
        (invertingCoefficientExtension M).map g.asHom ≫
          ((invertingCoefficientRestrictionIso M).app i).hom).hom v :=
  invertingCoefficientRootAction_apply M i g v

end InvertingCoefficientPublicCharacteristicsTests

#check CategoryTheory.CategoryHomology.invertingCoefficientRootTransport_comp_cocone
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientRootTransport_comp_cocone
#check CategoryTheory.CategoryHomology.invertingCoefficientColimitCoinvariantsIso_class
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientColimitCoinvariantsIso_class
#check CategoryTheory.CategoryHomology.invertingCoefficientHomologyZeroCoinvariantsIso_object_class
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientHomologyZeroCoinvariantsIso_object_class

namespace InvertingCoefficientPublicTransportTests

variable {J : Type uJ} [Category.{vJ} J] (M : J ⥤ AddCommGrpCat.{uA})
  [∀ {i j : J} (f : i ⟶ j), IsIso (M.map f)] [(CategoryTheory.nerve J).IsConnected]

example (s : Cocone M) (i j : J) :
    invertingCoefficientRootTransport M i j ≫ s.ι.app i = s.ι.app j :=
  invertingCoefficientRootTransport_comp_cocone M s i j

variable [HasColimit M] [HasCoproducts.{max uJ vJ} AddCommGrpCat.{uA}]

example (i j : J) :
    colimit.ι M j ≫ (invertingCoefficientColimitCoinvariantsIso M i).hom =
      invertingCoefficientRootTransport M i j ≫ AddCommGrpCat.ofHom
        (Representation.Coinvariants.mk (invertingCoefficientRootAction M i)).toAddMonoidHom :=
  invertingCoefficientColimitCoinvariantsIso_class M i j

example (i j : J) :
    coefficientHomologyClass M j ≫ (invertingCoefficientHomologyZeroCoinvariantsIso M i).hom =
      invertingCoefficientRootTransport M i j ≫ AddCommGrpCat.ofHom
        (Representation.Coinvariants.mk (invertingCoefficientRootAction M i)).toAddMonoidHom :=
  invertingCoefficientHomologyZeroCoinvariantsIso_object_class M i j

end InvertingCoefficientPublicTransportTests
