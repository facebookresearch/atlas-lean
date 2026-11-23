/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.CGWHBaseFunctoriality
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for one-map CGWH local-coefficient functoriality

These clients verify that pullback, the singular coefficient comparison, and
the single chain map are exactly the underlying TopCat constructions.  The
compact-probe universe is varied independently. Identity/composition laws
remain deliberately absent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uK uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHBaseFunctorialityTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y : CGWH.{uK, uX}}
variable (f : X ⟶ Y) (L : CGWH.LocalSystem R Y)

example : CGWH.LocalSystem R X := L.pullback f

example :
    (L.toSingular).pullback (TopCat.toSSet.map
        (CGWH.cgwhToTop.map f)) ≅
      (L.pullback f).toSingular :=
  CGWH.LocalSystem.singularPullbackIso f L

example :
    (L.pullback f).toSingular ⟶
      (L.toSingular).pullback (TopCat.toSSet.map
        (CGWH.cgwhToTop.map f)) :=
  (CGWH.LocalSystem.singularPullbackIso f L).inv

example :
    CGWH.localCoefficientChainComplex (L.pullback f) ⟶
      CGWH.localCoefficientChainComplex L :=
  CGWH.localCoefficientPullbackChainMap f L

example {x y : (TopCat.toSSet.obj X.toTop) _⦋0⦌}
    (e : (TopCat.toSSet.obj X.toTop).Edge x y) :
    ((L.toSingular).pullback (TopCat.toSSet.map
        (CGWH.cgwhToTop.map f))).map
          (SSet.FundamentalGroupoid.homMk e) ≫
      (CGWH.LocalSystem.singularPullbackIso f L).hom.app
        (SSet.FundamentalGroupoid.mk y) =
    (CGWH.LocalSystem.singularPullbackIso f L).hom.app
        (SSet.FundamentalGroupoid.mk x) ≫
      (L.pullback f).toSingular.map
        (SSet.FundamentalGroupoid.homMk e) :=
  CGWH.LocalSystem.singularPullbackIso_hom_naturality_homMk f L e

end Generic

section ZeroRing

variable {X Y : CGWH.{uK, uX}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem (ZMod 1) Y)

example :
    CGWH.localCoefficientChainComplex (L.pullback f) ⟶
      CGWH.localCoefficientChainComplex L :=
  CGWH.localCoefficientPullbackChainMap f L

end ZeroRing

section RaisedCarrierUniverse

variable (R : Type 1) [CommRing R]
variable {X Y : CGWH.{3, 2}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem R Y)

example :
    CGWH.localCoefficientChainComplex (L.pullback f) ⟶
      CGWH.localCoefficientChainComplex L :=
  CGWH.localCoefficientPullbackChainMap f L

end RaisedCarrierUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable {X Y : CGWH.{3, 1}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem R Y)

example :
    CGWH.localCoefficientChainComplex (L.pullback f) ⟶
      CGWH.localCoefficientChainComplex L :=
  CGWH.localCoefficientPullbackChainMap f L

end RaisedRingUniverse

section IndependentCompactProbeUniverse

variable (R : Type 1) [CommRing R]
variable {X Y : CGWH.{4, 1}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem R Y)

example :
    CGWH.localCoefficientChainComplex (L.pullback f) ⟶
      CGWH.localCoefficientChainComplex L :=
  CGWH.localCoefficientPullbackChainMap f L

end IndependentCompactProbeUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPullbackChainMap_id

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPullbackChainMap_comp

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPullbackHomologyMap

#guard_msgs (error, substring := true) in
#check CGWH.IsLocalCoefficientHomologyEquivalence

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPlusEquivalence

end StoppingBoundary

#print axioms CGWH.LocalSystem.pullback
#print axioms CGWH.LocalSystem.singularPullbackIso
#print axioms
  CGWH.LocalSystem.singularPullbackIso_hom_naturality_homMk
#print axioms CGWH.localCoefficientPullbackChainMap

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHBaseFunctorialityTests
