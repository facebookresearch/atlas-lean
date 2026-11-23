/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.CGWHHomology
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for CGWH local-coefficient homology

These clients verify the thin underlying-TopCat wrappers for natural
transformations, homology maps and functors, and constant coefficients. The
ring, carrier, and compact-probe universes are varied independently.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uK uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHHomologyTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X : CGWH.{uK, uX}}
variable (L K P : CGWH.LocalSystem R X)
variable (alpha : L ⟶ K) (beta : K ⟶ P)

example : L.toSingular ⟶ K.toSingular :=
  CGWH.LocalSystem.toSingularMap alpha

example (x : SSet.FundamentalGroupoid
    (TopCat.toSSet.obj X.toTop)) :
    (CGWH.LocalSystem.toSingularMap alpha).app x =
      alpha.app ((TopCat.singularFundamentalGroupoidFunctor
        X.toTop).obj x) :=
  CGWH.LocalSystem.toSingularMap_app alpha x

example : CGWH.LocalSystem.toSingularMap (𝟙 L) =
    𝟙 L.toSingular :=
  CGWH.LocalSystem.toSingularMap_id

example : CGWH.LocalSystem.toSingularMap (alpha ≫ beta) =
    CGWH.LocalSystem.toSingularMap alpha ≫
      CGWH.LocalSystem.toSingularMap beta :=
  CGWH.LocalSystem.toSingularMap_comp alpha beta

example (n : ℕ) : ModuleCat.{max uR uX} R :=
  CGWH.localCoefficientHomology L n

example (n : ℕ) :
    CGWH.localCoefficientHomology L n ⟶
      CGWH.localCoefficientHomology K n :=
  CGWH.localCoefficientHomologyMap alpha n

example (n : ℕ) :
    CGWH.localCoefficientHomologyMap (𝟙 L) n = 𝟙 _ :=
  CGWH.localCoefficientHomologyMap_id n

example (n : ℕ) :
    CGWH.localCoefficientHomologyMap (alpha ≫ beta) n =
      CGWH.localCoefficientHomologyMap alpha n ≫
        CGWH.localCoefficientHomologyMap beta n :=
  CGWH.localCoefficientHomologyMap_comp alpha beta n

example (n : ℕ) :
    CGWH.LocalSystem R X ⥤ ModuleCat.{max uR uX} R :=
  CGWH.localCoefficientHomologyFunctor n

example (n : ℕ) :
    (CGWH.localCoefficientHomologyFunctor n).obj L =
      CGWH.localCoefficientHomology L n :=
  CGWH.localCoefficientHomologyFunctor_obj L n

example (n : ℕ) :
    (CGWH.localCoefficientHomologyFunctor n).map alpha =
      CGWH.localCoefficientHomologyMap alpha n :=
  CGWH.localCoefficientHomologyFunctor_map alpha n

end Generic

section Constant

variable {R : Type uR} [CommRing R]
variable {X : CGWH.{uK, uX}}
variable (M : ModuleCat.{max uR uX} R) (n : ℕ)

example :
    CGWH.localCoefficientHomology
        (CGWH.constantLocalSystem (X := X) M) n ≅
      ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{max uR uX} R) n).obj M).obj X.toTop :=
  CGWH.constantLocalCoefficientHomologyIso (X := X) M n

example :
    (CGWH.constantLocalCoefficientHomologyIso
      (X := X) M n).hom =
      HomologicalComplex.homologyMap
        (CGWH.constantLocalCoefficientChainIso (X := X) M).hom n :=
  CGWH.constantLocalCoefficientHomologyIso_hom (X := X) M n

example :
    (CGWH.constantLocalCoefficientHomologyIso
      (X := X) M n).inv =
      HomologicalComplex.homologyMap
        (CGWH.constantLocalCoefficientChainIso (X := X) M).inv n :=
  CGWH.constantLocalCoefficientHomologyIso_inv (X := X) M n

end Constant

section Point

variable {R : Type uR} [CommRing R]
variable (L : CGWH.LocalSystem R
  (CGWH.of PUnit : CGWH.{uK, 0}))

example (n : ℕ) : ModuleCat.{uR} R :=
  CGWH.localCoefficientHomology L n

end Point

section ZeroRing

variable {X : CGWH.{uK, uX}}
variable (L : CGWH.LocalSystem (ZMod 1) X)

example (n : ℕ) : ModuleCat.{uX} (ZMod 1) :=
  CGWH.localCoefficientHomology L n

end ZeroRing

section RaisedCarrierUniverse

variable (R : Type 1) [CommRing R]
variable (X : CGWH.{3, 2}) (L : CGWH.LocalSystem R X)

example (n : ℕ) : ModuleCat.{2} R :=
  CGWH.localCoefficientHomology L n

example (n : ℕ) :
    CGWH.LocalSystem R X ⥤ ModuleCat.{2} R :=
  CGWH.localCoefficientHomologyFunctor n

end RaisedCarrierUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable (X : CGWH.{3, 1}) (L : CGWH.LocalSystem R X)
variable (M : ModuleCat.{2} R)

example (n : ℕ) : ModuleCat.{2} R :=
  CGWH.localCoefficientHomology L n

example (n : ℕ) :
    CGWH.localCoefficientHomology
        (CGWH.constantLocalSystem (X := X) M) n ≅
      ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{2} R) n).obj M).obj X.toTop :=
  CGWH.constantLocalCoefficientHomologyIso (X := X) M n

end RaisedRingUniverse

section IndependentCompactProbeUniverse

variable (R : Type 1) [CommRing R]
variable (X : CGWH.{4, 1}) (L : CGWH.LocalSystem R X)

example (n : ℕ) : ModuleCat.{1} R :=
  CGWH.localCoefficientHomology L n

example (n : ℕ) :
    CGWH.LocalSystem R X ⥤ ModuleCat.{1} R :=
  CGWH.localCoefficientHomologyFunctor n

end IndependentCompactProbeUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientSpaceMap

#guard_msgs (error, substring := true) in
#check CGWH.IsLocalCoefficientHomologyEquivalence

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPlusEquivalence

end StoppingBoundary

#print axioms CGWH.LocalSystem.toSingularMap
#print axioms CGWH.LocalSystem.toSingularMap_app
#print axioms CGWH.LocalSystem.toSingularMap_id
#print axioms CGWH.LocalSystem.toSingularMap_comp
#print axioms CGWH.localCoefficientHomology
#print axioms CGWH.localCoefficientHomologyMap
#print axioms CGWH.localCoefficientHomologyMap_id
#print axioms CGWH.localCoefficientHomologyMap_comp
#print axioms CGWH.localCoefficientHomologyFunctor
#print axioms CGWH.localCoefficientHomologyFunctor_obj
#print axioms CGWH.localCoefficientHomologyFunctor_map
#print axioms CGWH.constantLocalCoefficientHomologyIso
#print axioms CGWH.constantLocalCoefficientHomologyIso_hom
#print axioms CGWH.constantLocalCoefficientHomologyIso_inv

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHHomologyTests
