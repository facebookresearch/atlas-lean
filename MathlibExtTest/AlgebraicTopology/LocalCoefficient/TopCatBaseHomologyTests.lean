/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomology
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for map-level TopCat local-coefficient homology

These clients pin the variance, the exact homology-map formula, the
integral predicate, and independent ring/space universes.  The identity-map
test checks only its type shape; no pending pullback coherence law is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y : TopCat.{uX}}
variable (f : X ⟶ Y) (L : TopCat.LocalSystem R Y)

example (n : ℕ) :
    TopCat.localCoefficientHomology (L.pullback f) n ⟶
      TopCat.localCoefficientHomology L n :=
  TopCat.localCoefficientPullbackHomologyMap f L n

example (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap f L n =
      HomologicalComplex.homologyMap
        (TopCat.localCoefficientPullbackChainMap f L) n :=
  TopCat.localCoefficientPullbackHomologyMap_eq_homologyMap f L n

variable {K : TopCat.LocalSystem R Y} (alpha : L ⟶ K)

example (n : ℕ) :
    TopCat.localCoefficientHomology L n ⟶
      TopCat.localCoefficientHomology K n :=
  TopCat.localCoefficientHomologyMap alpha n

end Generic

section IdentityMapTypeShape

variable {R : Type uR} [CommRing R]
variable (X : TopCat.{uX}) (L : TopCat.LocalSystem R X)

example (n : ℕ) :
    TopCat.localCoefficientHomology (L.pullback (𝟙 X)) n ⟶
      TopCat.localCoefficientHomology L n :=
  TopCat.localCoefficientPullbackHomologyMap (𝟙 X) L n

end IdentityMapTypeShape

section IntegralPredicate

variable {X Y : TopCat.{uX}} (f : X ⟶ Y)

example : Prop := TopCat.IsLocalCoefficientHomologyEquivalence f

example (h : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (L : TopCat.LocalSystem ℤ Y) (n : ℕ) :
    IsIso (TopCat.localCoefficientPullbackHomologyMap f L n) :=
  h L n

end IntegralPredicate

section ZeroRing

variable {X Y : TopCat.{uX}} (f : X ⟶ Y)
variable (L : TopCat.LocalSystem (ZMod 1) Y)

example (n : ℕ) :
    TopCat.localCoefficientHomology (L.pullback f) n ⟶
      TopCat.localCoefficientHomology L n :=
  TopCat.localCoefficientPullbackHomologyMap f L n

end ZeroRing

section RaisedCarrierUniverse

variable (R : Type 1) [CommRing R]
variable {X Y : TopCat.{2}} (f : X ⟶ Y)
variable (L : TopCat.LocalSystem R Y)

example (n : ℕ) : ModuleCat.{2} R :=
  TopCat.localCoefficientHomology (L.pullback f) n

example (n : ℕ) :
    TopCat.localCoefficientHomology (L.pullback f) n ⟶
      TopCat.localCoefficientHomology L n :=
  TopCat.localCoefficientPullbackHomologyMap f L n

example : Prop := TopCat.IsLocalCoefficientHomologyEquivalence f

end RaisedCarrierUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable {X Y : TopCat.{1}} (f : X ⟶ Y)
variable (L : TopCat.LocalSystem R Y)

example (n : ℕ) : ModuleCat.{2} R :=
  TopCat.localCoefficientHomology (L.pullback f) n

example (n : ℕ) :
    TopCat.localCoefficientHomology (L.pullback f) n ⟶
      TopCat.localCoefficientHomology L n :=
  TopCat.localCoefficientPullbackHomologyMap f L n

end RaisedRingUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackHomologyMap_id

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackHomologyMap_comp

#guard_msgs (error, substring := true) in
#check TopCat.constantLocalCoefficientPullbackHomologyMap_naturality

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence.isIntegral

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence.isPlusConstructionAlong

end StoppingBoundary

#print axioms TopCat.localCoefficientPullbackHomologyMap
#print axioms TopCat.localCoefficientPullbackHomologyMap_eq_homologyMap
#print axioms TopCat.IsLocalCoefficientHomologyEquivalence

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyTests
