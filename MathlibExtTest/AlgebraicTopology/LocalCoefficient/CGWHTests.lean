/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.CGWH
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for CGWH local-coefficient chains

These clients verify that the CGWH API is exactly the TopCat construction on
the underlying space, including the represented-point and forward-edge
formulas.  Raised clients vary the ring, carrier, and compact-probe universes
independently.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe uR uK uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X : CGWH.{uK, uX}}
variable (L : CGWH.LocalSystem R X)

example : TopCat.LocalSystem R X.toTop := L

example : SSet.LocalSystem R (TopCat.toSSet.obj X.toTop) :=
  L.toSingular

example (x : (TopCat.toSSet.obj X.toTop) _⦋0⦌) :
    L.toSingular.obj (SSet.FundamentalGroupoid.mk x) =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) :=
  CGWH.LocalSystem.toSingular_obj_mk L x

example {x y : (TopCat.toSSet.obj X.toTop) _⦋0⦌}
    (e : (TopCat.toSSet.obj X.toTop).Edge x y) :
    L.toSingular.map (SSet.FundamentalGroupoid.homMk e) =
      L.map (Path.Homotopic.Quotient.mk
        ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
          (TopCat.counit_realizedVertex x)
          (TopCat.counit_realizedVertex y))) :=
  CGWH.LocalSystem.toSingular_map_homMk L e

example (n : ℕ) :
    (TopCat.toSSet.obj X.toTop) _⦋n⦌ →
      ModuleCat.{max uR uX} R :=
  CGWH.localCoefficientFamily L n

example (x : (TopCat.toSSet.obj X.toTop) _⦋0⦌) :
    CGWH.localCoefficientFamily L 0 x =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) :=
  CGWH.localCoefficientFamily_zero L x

example : SimplicialObject (ModuleCat.{max uR uX} R) :=
  CGWH.localCoefficientSimplicial L

example (n : ℕ) :
    (CGWH.localCoefficientSimplicial L).obj
        (op (SimplexCategory.mk n)) =
      CGWH.localCoefficientObj L n :=
  CGWH.localCoefficientSimplicial_obj L n

example {n : ℕ} (i : Fin (n + 2)) :
    (CGWH.localCoefficientSimplicial L).map
        (SimplexCategory.δ i).op =
      CGWH.localCoefficientFace L i :=
  CGWH.localCoefficientSimplicial_map_δ L i

example {n : ℕ} (i : Fin (n + 1)) :
    (CGWH.localCoefficientSimplicial L).map
        (SimplexCategory.σ i).op =
      CGWH.localCoefficientDegeneracy L i :=
  CGWH.localCoefficientSimplicial_map_σ L i

example : ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  CGWH.localCoefficientChainComplex L

example (n : ℕ) :
    (CGWH.localCoefficientChainComplex L).X n =
      CGWH.localCoefficientObj L n :=
  CGWH.localCoefficientChainComplex_X L n

example (n : ℕ) :
    (CGWH.localCoefficientChainComplex L).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        CGWH.localCoefficientFace L i :=
  CGWH.localCoefficientChainComplex_d L n

end Generic

section Point

variable {R : Type uR} [CommRing R]
variable (L : CGWH.LocalSystem R
  (CGWH.of PUnit : CGWH.{uK, 0}))

example : SimplicialObject (ModuleCat.{uR} R) :=
  CGWH.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{uR} R) ℕ :=
  CGWH.localCoefficientChainComplex L

end Point

section RaisedCarrierUniverse

variable (R : Type 1) [CommRing R]
variable (X : CGWH.{3, 2}) (L : CGWH.LocalSystem R X)

example : SimplicialObject (ModuleCat.{2} R) :=
  CGWH.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{2} R) ℕ :=
  CGWH.localCoefficientChainComplex L

end RaisedCarrierUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable (X : CGWH.{3, 1}) (L : CGWH.LocalSystem R X)

example : SimplicialObject (ModuleCat.{2} R) :=
  CGWH.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{2} R) ℕ :=
  CGWH.localCoefficientChainComplex L

end RaisedRingUniverse

section IndependentCompactProbeUniverse

variable (R : Type 1) [CommRing R]
variable (X : CGWH.{4, 1}) (L : CGWH.LocalSystem R X)

-- The compact-probe universe `4` does not inflate the coefficient target.
example : SimplicialObject (ModuleCat.{1} R) :=
  CGWH.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{1} R) ℕ :=
  CGWH.localCoefficientChainComplex L

end IndependentCompactProbeUniverse

section ZeroRing

variable {X : CGWH.{uK, uX}}
variable (L : CGWH.LocalSystem (ZMod 1) X)

example : ChainComplex (ModuleCat.{uX} (ZMod 1)) ℕ :=
  CGWH.localCoefficientChainComplex L

end ZeroRing

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check CGWH.LocalSystem.pullback

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientMap

#guard_msgs (error, substring := true) in
#check CGWH.localCoefficientHomology

#guard_msgs (error, substring := true) in
#check CGWH.constantLocalCoefficientChainIso

end StoppingBoundary

#print axioms CGWH.LocalSystem.toSingular_obj_mk
#print axioms CGWH.LocalSystem.toSingular_map_homMk
#print axioms CGWH.localCoefficientFamily_zero
#print axioms CGWH.localCoefficientSimplicial
#print axioms CGWH.localCoefficientSimplicial_obj
#print axioms CGWH.localCoefficientSimplicial_map_δ
#print axioms CGWH.localCoefficientSimplicial_map_σ
#print axioms CGWH.localCoefficientChainComplex
#print axioms CGWH.localCoefficientChainComplex_X
#print axioms CGWH.localCoefficientChainComplex_d

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.CGWHTests
