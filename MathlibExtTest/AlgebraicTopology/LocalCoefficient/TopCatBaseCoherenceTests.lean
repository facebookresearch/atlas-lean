/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseCoherence
public import Mathlib.Data.ZMod.Basic

/-! # Tests for TopCat local-coefficient pullback coherence -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseCoherenceTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y Z : TopCat.{uX}}
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable (L : TopCat.LocalSystem R Z)

example : L.pullback (𝟙 Z) ≅ L :=
  TopCat.LocalSystem.pullbackIdIso L

example : L.pullback (f ≫ g) ≅ (L.pullback g).pullback f :=
  TopCat.LocalSystem.pullbackCompIso f g L

example (x : _root_.FundamentalGroupoid Z) :
    (TopCat.LocalSystem.pullbackIdIso L).hom.app x = 𝟙 _ :=
  TopCat.LocalSystem.pullbackIdIso_hom_app L x

example (x : _root_.FundamentalGroupoid X) :
    (TopCat.LocalSystem.pullbackCompIso f g L).hom.app x = 𝟙 _ :=
  TopCat.LocalSystem.pullbackCompIso_hom_app f g L x

example :
    L.toSingular.pullback (TopCat.toSSet.map (f ≫ g)) ≅
      (L.toSingular.pullback (TopCat.toSSet.map g)).pullback
        (TopCat.toSSet.map f) :=
  TopCat.LocalSystem.sSetPullbackCompIso f g L

example :
    Functor.whiskerLeft
          (TopCat.singularFundamentalGroupoidFunctor X)
          (TopCat.LocalSystem.pullbackCompIso f g L).hom ≫
        (TopCat.LocalSystem.singularPullbackIso
          f (L.pullback g)).inv ≫
        Functor.whiskerLeft
          (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))
          (TopCat.LocalSystem.singularPullbackIso g L).inv =
      (TopCat.LocalSystem.singularPullbackIso (f ≫ g) L).inv ≫
        (TopCat.LocalSystem.sSetPullbackCompIso f g L).hom :=
  TopCat.LocalSystem.singularPullbackIso_comp f g L

example :
    TopCat.localCoefficientPullbackChainMap (f ≫ g) L =
      SSet.localCoefficientChainMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X)
            (TopCat.LocalSystem.pullbackCompIso f g L).hom) ≫
        TopCat.localCoefficientPullbackChainMap f (L.pullback g) ≫
        TopCat.localCoefficientPullbackChainMap g L :=
  TopCat.localCoefficientPullbackChainMap_comp f g L

end Generic

section Identity

variable {R : Type uR} [CommRing R]
variable (X : TopCat.{uX}) (L : TopCat.LocalSystem R X)

example :
    (TopCat.LocalSystem.singularPullbackIso (𝟙 X) L).inv ≫
        (TopCat.LocalSystem.sSetPullbackIdIso L).hom =
      Functor.whiskerLeft
        (TopCat.singularFundamentalGroupoidFunctor X)
        (TopCat.LocalSystem.pullbackIdIso L).hom :=
  TopCat.LocalSystem.singularPullbackIso_id L

example :
    TopCat.localCoefficientPullbackChainMap (𝟙 X) L =
      SSet.localCoefficientChainMap
        (Functor.whiskerLeft
          (TopCat.singularFundamentalGroupoidFunctor X)
          (TopCat.LocalSystem.pullbackIdIso L).hom) :=
  TopCat.localCoefficientPullbackChainMap_id L

end Identity

section NonidentityComposite

private noncomputable def collapse : TopCat.I ⟶ TopCat.I :=
  TopCat.const (X := TopCat.I) (0 : TopCat.I)

example : collapse (1 : TopCat.I) = 0 := rfl

variable (L : TopCat.LocalSystem (ZMod 1) TopCat.I)

example :
    TopCat.localCoefficientPullbackChainMap (collapse ≫ collapse) L =
      SSet.localCoefficientChainMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor TopCat.I)
            (TopCat.LocalSystem.pullbackCompIso
              collapse collapse L).hom) ≫
        TopCat.localCoefficientPullbackChainMap collapse
          (L.pullback collapse) ≫
        TopCat.localCoefficientPullbackChainMap collapse L :=
  TopCat.localCoefficientPullbackChainMap_comp collapse collapse L

end NonidentityComposite

section IndependentUniverses

variable (R₁ : Type 1) [CommRing R₁]
variable {X₂ Y₂ Z₂ : TopCat.{2}}
variable (f₂ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂)
variable (L₁ : TopCat.LocalSystem R₁ Z₂)

example :
    TopCat.localCoefficientPullbackChainMap (f₂ ≫ g₂) L₁ =
      SSet.localCoefficientChainMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X₂)
            (TopCat.LocalSystem.pullbackCompIso f₂ g₂ L₁).hom) ≫
        TopCat.localCoefficientPullbackChainMap f₂ (L₁.pullback g₂) ≫
        TopCat.localCoefficientPullbackChainMap g₂ L₁ :=
  TopCat.localCoefficientPullbackChainMap_comp f₂ g₂ L₁

variable (R₂ : Type 2) [CommRing R₂]
variable {X₁ Y₁ Z₁ : TopCat.{1}}
variable (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁)
variable (L₂ : TopCat.LocalSystem R₂ Z₁)

example :
    TopCat.localCoefficientPullbackChainMap (f₁ ≫ g₁) L₂ =
      SSet.localCoefficientChainMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X₁)
            (TopCat.LocalSystem.pullbackCompIso f₁ g₁ L₂).hom) ≫
        TopCat.localCoefficientPullbackChainMap f₁ (L₂.pullback g₁) ≫
        TopCat.localCoefficientPullbackChainMap g₁ L₂ :=
  TopCat.localCoefficientPullbackChainMap_comp f₁ g₁ L₂

end IndependentUniverses

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPullbackChainMap_comp

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackHomologyMap_comp

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence

end StoppingBoundary

#print axioms TopCat.LocalSystem.pullbackIdIso
#print axioms TopCat.LocalSystem.pullbackCompIso
#print axioms TopCat.LocalSystem.pullbackIdIso_hom_app
#print axioms TopCat.LocalSystem.pullbackCompIso_hom_app
#print axioms TopCat.LocalSystem.sSetPullbackIdIso
#print axioms TopCat.LocalSystem.sSetPullbackCompIso
#print axioms TopCat.LocalSystem.singularPullbackIso_id
#print axioms TopCat.LocalSystem.singularPullbackIso_comp
#print axioms TopCat.localCoefficientPullbackChainMap_id
#print axioms TopCat.localCoefficientPullbackChainMap_comp

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseCoherenceTests
