/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatHomology
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for TopCat local-coefficient homology

These clients exercise singular whiskering, homology maps and their laws,
the fixed-degree functor, and the native constant-system comparison. Point,
zero-ring, and independent-universe cases pin the intended scope.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatHomologyTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X : TopCat.{uX}}
variable (L K P : TopCat.LocalSystem R X)
variable (alpha : L ⟶ K) (beta : K ⟶ P)

example : L.toSingular ⟶ K.toSingular :=
  TopCat.LocalSystem.toSingularMap alpha

example (x : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (TopCat.LocalSystem.toSingularMap alpha).app x =
      alpha.app ((TopCat.singularFundamentalGroupoidFunctor X).obj x) :=
  TopCat.LocalSystem.toSingularMap_app alpha x

example : TopCat.LocalSystem.toSingularMap (𝟙 L) =
    𝟙 L.toSingular :=
  TopCat.LocalSystem.toSingularMap_id

example : TopCat.LocalSystem.toSingularMap (alpha ≫ beta) =
    TopCat.LocalSystem.toSingularMap alpha ≫
      TopCat.LocalSystem.toSingularMap beta :=
  TopCat.LocalSystem.toSingularMap_comp alpha beta

example (n : ℕ) : ModuleCat.{max uR uX} R :=
  TopCat.localCoefficientHomology L n

example (n : ℕ) :
    TopCat.localCoefficientHomology L n ⟶
      TopCat.localCoefficientHomology K n :=
  TopCat.localCoefficientHomologyMap alpha n

example (n : ℕ) :
    TopCat.localCoefficientHomologyMap (𝟙 L) n = 𝟙 _ :=
  TopCat.localCoefficientHomologyMap_id n

example (n : ℕ) :
    TopCat.localCoefficientHomologyMap (alpha ≫ beta) n =
      TopCat.localCoefficientHomologyMap alpha n ≫
        TopCat.localCoefficientHomologyMap beta n :=
  TopCat.localCoefficientHomologyMap_comp alpha beta n

example (n : ℕ) :
    TopCat.LocalSystem R X ⥤ ModuleCat.{max uR uX} R :=
  TopCat.localCoefficientHomologyFunctor n

example (n : ℕ) :
    (TopCat.localCoefficientHomologyFunctor n).obj L =
      TopCat.localCoefficientHomology L n :=
  TopCat.localCoefficientHomologyFunctor_obj L n

example (n : ℕ) :
    (TopCat.localCoefficientHomologyFunctor n).map alpha =
      TopCat.localCoefficientHomologyMap alpha n :=
  TopCat.localCoefficientHomologyFunctor_map alpha n

end Generic

section Constant

variable {R : Type uR} [CommRing R]
variable {X : TopCat.{uX}}
variable (M : ModuleCat.{max uR uX} R) (n : ℕ)

example :
    TopCat.localCoefficientHomology
        (TopCat.constantLocalSystem (X := X) M) n ≅
      ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{max uR uX} R) n).obj M).obj X :=
  TopCat.constantLocalCoefficientHomologyIso (X := X) M n

example :
    (TopCat.constantLocalCoefficientHomologyIso
      (X := X) M n).hom =
      HomologicalComplex.homologyMap
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom n :=
  TopCat.constantLocalCoefficientHomologyIso_hom (X := X) M n

example :
    (TopCat.constantLocalCoefficientHomologyIso
      (X := X) M n).inv =
      HomologicalComplex.homologyMap
        (TopCat.constantLocalCoefficientChainIso (X := X) M).inv n :=
  TopCat.constantLocalCoefficientHomologyIso_inv (X := X) M n

end Constant

section Point

variable {R : Type uR} [CommRing R]
variable (L : TopCat.LocalSystem R (TopCat.of PUnit))

example (n : ℕ) : ModuleCat.{uR} R :=
  TopCat.localCoefficientHomology L n

example (n : ℕ) :
    (TopCat.localCoefficientHomologyFunctor n).obj L =
      TopCat.localCoefficientHomology L n :=
  TopCat.localCoefficientHomologyFunctor_obj L n

end Point

section ZeroRing

variable {X : TopCat.{uX}}
variable (L : TopCat.LocalSystem (ZMod 1) X)

example (n : ℕ) : ModuleCat.{uX} (ZMod 1) :=
  TopCat.localCoefficientHomology L n

end ZeroRing

section RaisedCarrierUniverse

variable (R : Type 1) [CommRing R]
variable (X : TopCat.{2}) (L : TopCat.LocalSystem R X)

example (n : ℕ) : ModuleCat.{2} R :=
  TopCat.localCoefficientHomology L n

example (n : ℕ) :
    TopCat.LocalSystem R X ⥤ ModuleCat.{2} R :=
  TopCat.localCoefficientHomologyFunctor n

end RaisedCarrierUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable (X : TopCat.{1}) (L : TopCat.LocalSystem R X)
variable (M : ModuleCat.{2} R)

example (n : ℕ) : ModuleCat.{2} R :=
  TopCat.localCoefficientHomology L n

example (n : ℕ) :
    TopCat.localCoefficientHomology
        (TopCat.constantLocalSystem (X := X) M) n ≅
      ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{2} R) n).obj M).obj X :=
  TopCat.constantLocalCoefficientHomologyIso (X := X) M n

end RaisedRingUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientSpaceMap

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPlusEquivalence

end StoppingBoundary

#print axioms TopCat.LocalSystem.toSingularMap
#print axioms TopCat.LocalSystem.toSingularMap_app
#print axioms TopCat.LocalSystem.toSingularMap_id
#print axioms TopCat.LocalSystem.toSingularMap_comp
#print axioms TopCat.localCoefficientHomology
#print axioms TopCat.localCoefficientHomologyMap
#print axioms TopCat.localCoefficientHomologyMap_id
#print axioms TopCat.localCoefficientHomologyMap_comp
#print axioms TopCat.localCoefficientHomologyFunctor
#print axioms TopCat.localCoefficientHomologyFunctor_obj
#print axioms TopCat.localCoefficientHomologyFunctor_map
#print axioms TopCat.constantLocalCoefficientHomologyIso
#print axioms TopCat.constantLocalCoefficientHomologyIso_hom
#print axioms TopCat.constantLocalCoefficientHomologyIso_inv

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatHomologyTests
