/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.CGWHBaseHomology
public import
  MathlibExt.AlgebraicTopology.PlusConstruction.HomologyCandidate
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for map-level CGWH local-coefficient homology

These clients verify the underlying-TopCat formula, the direct quantified
predicate, independent compact/carrier universes, and the stopping boundary
before ordinary integral homology and plus recognition.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uK uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHBaseHomologyTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y : CGWH.{uK, uX}}
variable (f : X ⟶ Y) (L : CGWH.LocalSystem R Y)

example (n : ℕ) :
    CGWH.localCoefficientHomology (L.pullback f) n ⟶
      CGWH.localCoefficientHomology L n :=
  CGWH.localCoefficientPullbackHomologyMap f L n

example (n : ℕ) :
    CGWH.localCoefficientPullbackHomologyMap f L n =
      TopCat.localCoefficientPullbackHomologyMap
        (CGWH.cgwhToTop.map f) L n :=
  CGWH.localCoefficientPullbackHomologyMap_eq_topCat f L n

end Generic

section IdentityMapTypeShape

variable {R : Type uR} [CommRing R]
variable (X : CGWH.{uK, uX}) (L : CGWH.LocalSystem R X)

example (n : ℕ) :
    CGWH.localCoefficientHomology (L.pullback (𝟙 X)) n ⟶
      CGWH.localCoefficientHomology L n :=
  CGWH.localCoefficientPullbackHomologyMap (𝟙 X) L n

end IdentityMapTypeShape

section IntegralPredicate

variable {X Y : CGWH.{uK, uX}} (f : X ⟶ Y)

example : Prop := CGWH.IsLocalCoefficientHomologyEquivalence f

example :
    CGWH.IsLocalCoefficientHomologyEquivalence f ↔
      ∀ (L : CGWH.LocalSystem ℤ Y) (n : ℕ),
        IsIso (CGWH.localCoefficientPullbackHomologyMap f L n) :=
  CGWH.isLocalCoefficientHomologyEquivalence_iff f

example (h : CGWH.IsLocalCoefficientHomologyEquivalence f)
    (L : CGWH.LocalSystem ℤ Y) (n : ℕ) :
    IsIso (CGWH.localCoefficientPullbackHomologyMap f L n) :=
  (CGWH.isLocalCoefficientHomologyEquivalence_iff f).mp h L n

example : Prop := CGWH.IsIntegralHomologyEquivalence f

end IntegralPredicate

section ZeroRing

variable {X Y : CGWH.{uK, uX}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem (ZMod 1) Y)

example (n : ℕ) :
    CGWH.localCoefficientHomology (L.pullback f) n ⟶
      CGWH.localCoefficientHomology L n :=
  CGWH.localCoefficientPullbackHomologyMap f L n

end ZeroRing

section RaisedCarrierUniverse

variable (R : Type 1) [CommRing R]
variable {X Y : CGWH.{3, 2}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem R Y)

example (n : ℕ) : ModuleCat.{2} R :=
  CGWH.localCoefficientHomology (L.pullback f) n

example (n : ℕ) :
    CGWH.localCoefficientHomology (L.pullback f) n ⟶
      CGWH.localCoefficientHomology L n :=
  CGWH.localCoefficientPullbackHomologyMap f L n

example : Prop := CGWH.IsLocalCoefficientHomologyEquivalence f

end RaisedCarrierUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable {X Y : CGWH.{3, 1}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem R Y)

example (n : ℕ) : ModuleCat.{2} R :=
  CGWH.localCoefficientHomology (L.pullback f) n

example (n : ℕ) :
    CGWH.localCoefficientHomology (L.pullback f) n ⟶
      CGWH.localCoefficientHomology L n :=
  CGWH.localCoefficientPullbackHomologyMap f L n

end RaisedRingUniverse

section IndependentCompactProbeUniverse

variable (R : Type 1) [CommRing R]
variable {X Y : CGWH.{4, 1}} (f : X ⟶ Y)
variable (L : CGWH.LocalSystem R Y)

example (n : ℕ) :
    CGWH.localCoefficientHomology (L.pullback f) n ⟶
      CGWH.localCoefficientHomology L n :=
  CGWH.localCoefficientPullbackHomologyMap f L n

example : Prop := CGWH.IsLocalCoefficientHomologyEquivalence f

end IndependentCompactProbeUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPullbackHomologyMap_id

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientPullbackHomologyMap_comp

#guard_msgs (error, substring := true) in
#check CGWH.constantLocalCoefficientPullbackHomologyMap_naturality

#guard_msgs (error, substring := true) in
#check CGWH.IsLocalCoefficientHomologyEquivalence.isIntegral

#guard_msgs (error, substring := true) in
#check CGWH.IsLocalCoefficientHomologyEquivalence.isPlusConstructionAlong

end StoppingBoundary

#print axioms CGWH.localCoefficientPullbackHomologyMap
#print axioms CGWH.localCoefficientPullbackHomologyMap_eq_topCat
#print axioms CGWH.IsLocalCoefficientHomologyEquivalence
#print axioms CGWH.isLocalCoefficientHomologyEquivalence_iff

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHBaseHomologyTests
