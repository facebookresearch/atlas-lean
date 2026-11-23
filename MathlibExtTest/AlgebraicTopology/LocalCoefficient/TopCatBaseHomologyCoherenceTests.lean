/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyCoherence
public import Mathlib.Data.ZMod.Basic

/-! # Tests for TopCat local-coefficient pullback homology coherence -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyCoherenceTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y Z : TopCat.{uX}}
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable (L : TopCat.LocalSystem R Z)

example (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap (f ≫ g) L n =
      SSet.localCoefficientHomologyMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X)
            (TopCat.LocalSystem.pullbackCompIso f g L).hom) n ≫
        TopCat.localCoefficientPullbackHomologyMap f (L.pullback g) n ≫
        TopCat.localCoefficientPullbackHomologyMap g L n :=
  TopCat.localCoefficientPullbackHomologyMap_comp f g L n

example :
    TopCat.localCoefficientPullbackHomologyMap (f ≫ g) L 0 =
      SSet.localCoefficientHomologyMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X)
            (TopCat.LocalSystem.pullbackCompIso f g L).hom) 0 ≫
        TopCat.localCoefficientPullbackHomologyMap f (L.pullback g) 0 ≫
        TopCat.localCoefficientPullbackHomologyMap g L 0 :=
  TopCat.localCoefficientPullbackHomologyMap_comp f g L 0

end Generic

section Identity

variable {R : Type uR} [CommRing R]
variable (X : TopCat.{uX}) (L : TopCat.LocalSystem R X)

example (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap (𝟙 X) L n =
      SSet.localCoefficientHomologyMap
        (Functor.whiskerLeft
          (TopCat.singularFundamentalGroupoidFunctor X)
          (TopCat.LocalSystem.pullbackIdIso L).hom) n :=
  TopCat.localCoefficientPullbackHomologyMap_id L n

end Identity

section NonidentityComposite

private noncomputable def collapse : TopCat.I ⟶ TopCat.I :=
  TopCat.const (X := TopCat.I) (0 : TopCat.I)

example : collapse (1 : TopCat.I) = 0 := rfl

variable (L : TopCat.LocalSystem (ZMod 1) TopCat.I)

example :
    TopCat.localCoefficientPullbackHomologyMap
        (collapse ≫ collapse) L 0 =
      SSet.localCoefficientHomologyMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor TopCat.I)
            (TopCat.LocalSystem.pullbackCompIso
              collapse collapse L).hom) 0 ≫
        TopCat.localCoefficientPullbackHomologyMap collapse
          (L.pullback collapse) 0 ≫
        TopCat.localCoefficientPullbackHomologyMap collapse L 0 :=
  TopCat.localCoefficientPullbackHomologyMap_comp collapse collapse L 0

end NonidentityComposite

section IndependentUniverses

variable (R₁ : Type 1) [CommRing R₁]
variable {X₂ Y₂ Z₂ : TopCat.{2}}
variable (f₂ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂)
variable (L₁ : TopCat.LocalSystem R₁ Z₂)

example (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap (f₂ ≫ g₂) L₁ n =
      SSet.localCoefficientHomologyMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X₂)
            (TopCat.LocalSystem.pullbackCompIso f₂ g₂ L₁).hom) n ≫
        TopCat.localCoefficientPullbackHomologyMap
          f₂ (L₁.pullback g₂) n ≫
        TopCat.localCoefficientPullbackHomologyMap g₂ L₁ n :=
  TopCat.localCoefficientPullbackHomologyMap_comp f₂ g₂ L₁ n

variable (R₂ : Type 2) [CommRing R₂]
variable {X₁ Y₁ Z₁ : TopCat.{1}}
variable (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁)
variable (L₂ : TopCat.LocalSystem R₂ Z₁)

example (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap (f₁ ≫ g₁) L₂ n =
      SSet.localCoefficientHomologyMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X₁)
            (TopCat.LocalSystem.pullbackCompIso f₁ g₁ L₂).hom) n ≫
        TopCat.localCoefficientPullbackHomologyMap
          f₁ (L₂.pullback g₁) n ≫
        TopCat.localCoefficientPullbackHomologyMap g₁ L₂ n :=
  TopCat.localCoefficientPullbackHomologyMap_comp f₁ g₁ L₂ n

end IndependentUniverses

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.isLocalCoefficientHomologyEquivalence_id

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackHomologyMap_isAcyclic

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackHomologyMap_isPlusConstruction

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.StableGL.liftedFiniteBGLTelescopeLocalCoefficientHomologyPlusCandidate

end StoppingBoundary

#print axioms TopCat.localCoefficientPullbackHomologyMap_id
#print axioms TopCat.localCoefficientPullbackHomologyMap_comp

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyCoherenceTests
