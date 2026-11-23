/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseFunctoriality
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for one-map TopCat local-coefficient functoriality

These clients pin the singular fundamental-groupoid comparison, the
singular-pullback coefficient Iso and its orientation, and the resulting
single chain map. A nonidentity interval collapse and its forward edge
naturality guard against an accidental inverse. Identity/composition laws
remain deliberately absent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseFunctorialityTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y : TopCat.{uX}}
variable (f : X ⟶ Y) (L : TopCat.LocalSystem R Y)

example : TopCat.LocalSystem R X := L.pullback f

example :
    SSet.mapFundamentalGroupoid (TopCat.toSSet.map f) ⋙
        TopCat.singularFundamentalGroupoidFunctor Y ≅
      TopCat.singularFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map f.hom :=
  TopCat.singularFundamentalGroupoidNaturality f

example :
    (L.toSingular).pullback (TopCat.toSSet.map f) ≅
      (L.pullback f).toSingular :=
  TopCat.LocalSystem.singularPullbackIso f L

example :
    (L.pullback f).toSingular ⟶
      (L.toSingular).pullback (TopCat.toSSet.map f) :=
  (TopCat.LocalSystem.singularPullbackIso f L).inv

example :
    TopCat.localCoefficientChainComplex (L.pullback f) ⟶
      TopCat.localCoefficientChainComplex L :=
  TopCat.localCoefficientPullbackChainMap f L

example (n : ℕ) :
    (TopCat.localCoefficientPullbackChainMap f L).f n =
      SSet.localCoefficientMap
          (TopCat.LocalSystem.singularPullbackIso f L).inv n ≫
        (SSet.localCoefficientPullbackChainMap
          (TopCat.toSSet.map f) L.toSingular).f n :=
  TopCat.localCoefficientPullbackChainMap_f f L n

end Generic

section NonidentityIntervalMap

private noncomputable def collapse : TopCat.I ⟶ TopCat.I :=
  TopCat.const (X := TopCat.I) (0 : TopCat.I)

example : collapse (1 : TopCat.I) = 0 := rfl

private noncomputable def intervalPath :
    TopCat.I.Path (0 : TopCat.I) 1 where
  hom := 𝟙 TopCat.I

private noncomputable def intervalEdge :
    (TopCat.toSSet.obj TopCat.I).Edge
      (TopCat.toSSetObj₀Equiv.symm (0 : TopCat.I))
      (TopCat.toSSetObj₀Equiv.symm (1 : TopCat.I)) :=
  TopCat.toSSetObjEdgeEquiv.symm intervalPath

variable {R : Type uR} [CommRing R]
variable (L : TopCat.LocalSystem R TopCat.I)

example :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map collapse) ⋙
        TopCat.singularFundamentalGroupoidFunctor TopCat.I).map
          (SSet.FundamentalGroupoid.homMk intervalEdge) ≫
      (TopCat.singularFundamentalGroupoidNaturality collapse).hom.app
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm (1 : TopCat.I))) =
    (TopCat.singularFundamentalGroupoidNaturality collapse).hom.app
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm (0 : TopCat.I))) ≫
      (TopCat.singularFundamentalGroupoidFunctor TopCat.I ⋙
        _root_.FundamentalGroupoid.map collapse.hom).map
          (SSet.FundamentalGroupoid.homMk intervalEdge) :=
  TopCat.singularFundamentalGroupoidNaturality_hom_naturality_homMk
    collapse intervalEdge

example :
    ((L.toSingular).pullback (TopCat.toSSet.map collapse)).map
        (SSet.FundamentalGroupoid.homMk intervalEdge) ≫
      (TopCat.LocalSystem.singularPullbackIso collapse L).hom.app
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm (1 : TopCat.I))) =
    (TopCat.LocalSystem.singularPullbackIso collapse L).hom.app
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm (0 : TopCat.I))) ≫
      (L.pullback collapse).toSingular.map
        (SSet.FundamentalGroupoid.homMk intervalEdge) :=
  TopCat.LocalSystem.singularPullbackIso_hom_naturality_homMk
    collapse L intervalEdge

example :
    TopCat.localCoefficientChainComplex (L.pullback collapse) ⟶
      TopCat.localCoefficientChainComplex L :=
  TopCat.localCoefficientPullbackChainMap collapse L

end NonidentityIntervalMap

section ZeroRing

variable {X Y : TopCat.{uX}} (f : X ⟶ Y)
variable (L : TopCat.LocalSystem (ZMod 1) Y)

example :
    TopCat.localCoefficientChainComplex (L.pullback f) ⟶
      TopCat.localCoefficientChainComplex L :=
  TopCat.localCoefficientPullbackChainMap f L

end ZeroRing

section RaisedCarrierUniverse

variable (R : Type 1) [CommRing R]
variable {X Y : TopCat.{2}} (f : X ⟶ Y)
variable (L : TopCat.LocalSystem R Y)

example :
    TopCat.localCoefficientChainComplex (L.pullback f) ⟶
      TopCat.localCoefficientChainComplex L :=
  TopCat.localCoefficientPullbackChainMap f L

end RaisedCarrierUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable {X Y : TopCat.{1}} (f : X ⟶ Y)
variable (L : TopCat.LocalSystem R Y)

example :
    TopCat.localCoefficientChainComplex (L.pullback f) ⟶
      TopCat.localCoefficientChainComplex L :=
  TopCat.localCoefficientPullbackChainMap f L

end RaisedRingUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackChainMap_id

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackChainMap_comp

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackHomologyMap

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPlusEquivalence

end StoppingBoundary

#print axioms TopCat.singularFundamentalGroupoidNaturality
#print axioms
  TopCat.singularFundamentalGroupoidNaturality_hom_naturality_homMk
#print axioms TopCat.LocalSystem.pullback
#print axioms TopCat.LocalSystem.singularPullbackIso
#print axioms
  TopCat.LocalSystem.singularPullbackIso_hom_naturality_homMk
#print axioms TopCat.localCoefficientPullbackChainMap
#print axioms TopCat.localCoefficientPullbackChainMap_f

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseFunctorialityTests
