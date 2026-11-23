/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetHomology
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCat
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for simplicial-set local-coefficient homology

These clients exercise homology objects and maps, identity and composition,
the fixed-degree functor, and the constant-system comparison. Point,
zero-ring, and independent raised-universe cases pin the intended boundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetHomologyTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable (L K P : SSet.LocalSystem R X)
variable (alpha : L ⟶ K) (beta : K ⟶ P)

example (n : ℕ) : ModuleCat.{max uR uX} R :=
  SSet.localCoefficientHomology L n

example (n : ℕ) :
    SSet.localCoefficientHomology L n ⟶
      SSet.localCoefficientHomology K n :=
  SSet.localCoefficientHomologyMap alpha n

example (n : ℕ) :
    SSet.localCoefficientHomologyMap (𝟙 L) n = 𝟙 _ :=
  SSet.localCoefficientHomologyMap_id n

example (n : ℕ) :
    SSet.localCoefficientHomologyMap (alpha ≫ beta) n =
      SSet.localCoefficientHomologyMap alpha n ≫
        SSet.localCoefficientHomologyMap beta n :=
  SSet.localCoefficientHomologyMap_comp alpha beta n

example (n : ℕ) :
    SSet.LocalSystem R X ⥤ ModuleCat.{max uR uX} R :=
  SSet.localCoefficientHomologyFunctor n

example (n : ℕ) :
    (SSet.localCoefficientHomologyFunctor n).obj L =
      SSet.localCoefficientHomology L n :=
  SSet.localCoefficientHomologyFunctor_obj L n

example (n : ℕ) :
    (SSet.localCoefficientHomologyFunctor n).map alpha =
      SSet.localCoefficientHomologyMap alpha n :=
  SSet.localCoefficientHomologyFunctor_map alpha n

end Generic

section Constant

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable (M : ModuleCat.{max uR uX} R) (n : ℕ)

example :
    SSet.localCoefficientHomology
        (SSet.constantLocalSystem (X := X) M) n ≅
      X.homology M n :=
  SSet.constantLocalCoefficientHomologyIso (X := X) M n

example :
    (SSet.constantLocalCoefficientHomologyIso
      (X := X) M n).hom =
      HomologicalComplex.homologyMap
        (SSet.constantLocalCoefficientChainIso (X := X) M).hom n :=
  SSet.constantLocalCoefficientHomologyIso_hom (X := X) M n

example :
    (SSet.constantLocalCoefficientHomologyIso
      (X := X) M n).inv =
      HomologicalComplex.homologyMap
        (SSet.constantLocalCoefficientChainIso (X := X) M).inv n :=
  SSet.constantLocalCoefficientHomologyIso_inv (X := X) M n

end Constant

section Point

variable {R : Type uR} [CommRing R]
variable (L : SSet.LocalSystem R Δ[0])

example (n : ℕ) : ModuleCat.{uR} R :=
  SSet.localCoefficientHomology L n

example (n : ℕ) :
    (SSet.localCoefficientHomologyFunctor n).obj L =
      SSet.localCoefficientHomology L n :=
  SSet.localCoefficientHomologyFunctor_obj L n

end Point

section ZeroRing

variable {X : SSet.{uX}}
variable (L : SSet.LocalSystem (ZMod 1) X)

example (n : ℕ) : ModuleCat.{uX} (ZMod 1) :=
  SSet.localCoefficientHomology L n

example (n : ℕ) :
    SSet.LocalSystem (ZMod 1) X ⥤ ModuleCat.{uX} (ZMod 1) :=
  SSet.localCoefficientHomologyFunctor n

end ZeroRing

section RaisedSimplexUniverse

variable (R : Type 1) [CommRing R]
variable (X : SSet.{2}) (L : SSet.LocalSystem R X)

example (n : ℕ) : ModuleCat.{2} R :=
  SSet.localCoefficientHomology L n

example (n : ℕ) :
    SSet.LocalSystem R X ⥤ ModuleCat.{2} R :=
  SSet.localCoefficientHomologyFunctor n

end RaisedSimplexUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable (X : SSet.{1}) (L : SSet.LocalSystem R X)
variable (M : ModuleCat.{2} R)

example (n : ℕ) : ModuleCat.{2} R :=
  SSet.localCoefficientHomology L n

example (n : ℕ) :
    SSet.localCoefficientHomology
        (SSet.constantLocalSystem (X := X) M) n ≅
      X.homology M n :=
  SSet.constantLocalCoefficientHomologyIso (X := X) M n

end RaisedRingUniverse

section StoppingBoundary

-- Base-simplicial-map functoriality is a separate packet.
#guard_msgs (error, substring := true) in
#check SSet.localCoefficientSpaceMap

-- The TopCat wrapper has not yet been lifted to homology.
#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientHomology

-- No local-coefficient equivalence or plus predicate is introduced here.
#guard_msgs (error, substring := true) in
#check SSet.IsLocalCoefficientHomologyEquivalence

#guard_msgs (error, substring := true) in
#check SSet.localCoefficientPlusEquivalence

end StoppingBoundary

#print axioms SSet.localCoefficientHomology
#print axioms SSet.localCoefficientHomologyMap
#print axioms SSet.localCoefficientHomologyMap_id
#print axioms SSet.localCoefficientHomologyMap_comp
#print axioms SSet.localCoefficientHomologyFunctor
#print axioms SSet.localCoefficientHomologyFunctor_obj
#print axioms SSet.localCoefficientHomologyFunctor_map
#print axioms SSet.constantLocalCoefficientHomologyIso
#print axioms SSet.constantLocalCoefficientHomologyIso_hom
#print axioms SSet.constantLocalCoefficientHomologyIso_inv

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetHomologyTests
