/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCat
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for TopCat local-coefficient chains

These clients pin the singular pullback, its represented-point and forward
singular-edge formulas, both degree-one face components, and the simplicial
and unnormalized chain-complex wrappers.  Point, interval-edge, zero-ring,
and independent-universe cases exercise the intended boundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X : TopCat.{uX}}
variable (L : TopCat.LocalSystem R X)

example : _root_.FundamentalGroupoid X ⥤
    ModuleCat.{max uR uX} R := L

example : SSet.LocalSystem R (TopCat.toSSet.obj X) :=
  L.toSingular

example (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    L.toSingular.obj (SSet.FundamentalGroupoid.mk x) =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) :=
  TopCat.LocalSystem.toSingular_obj_mk L x

example {x y : (TopCat.toSSet.obj X) _⦋0⦌}
    (e : (TopCat.toSSet.obj X).Edge x y) :
    L.toSingular.map (SSet.FundamentalGroupoid.homMk e) =
      L.map (Path.Homotopic.Quotient.mk
        ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
          (TopCat.counit_realizedVertex x)
          (TopCat.counit_realizedVertex y))) :=
  TopCat.LocalSystem.toSingular_map_homMk L e

section EdgeFaces

variable {x y : (TopCat.toSSet.obj X) _⦋0⦌}
variable (e : (TopCat.toSSet.obj X).Edge x y)

-- Before the LC1 endpoint casts, the zeroth component is exactly the
-- forward edge action.
example :
    coefficientFaceHom L.toSingular (0 : Fin 2)
        (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e)) =
      L.toSingular.map (SSet.FundamentalGroupoid.homMk e) := by
  rfl

-- The other component preserves the initial coefficient.
example :
    coefficientFaceHom L.toSingular (1 : Fin 2)
        (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e)) =
      𝟙 (L.toSingular.obj (SSet.FundamentalGroupoid.mk x)) := by
  change L.toSingular.map (𝟙 _) = _
  exact L.toSingular.map_id _

-- Exercise both actual degree-one maps through their coproduct summands.
example :
    nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit
          (TopCat.toSSet.obj X)) L.toSingular e.edge ≫
      TopCat.localCoefficientFace L (0 : Fin 2) =
    nervePullbackCoefficientFaceHom
        (SSet.fundamentalGroupoidNerveUnit
          (TopCat.toSSet.obj X)) L.toSingular 0 e.edge ≫
      nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit
          (TopCat.toSSet.obj X)) L.toSingular
            ((TopCat.toSSet.obj X).δ 0 e.edge) :=
  nervePullbackCoefficientι_face _ _ 0 e.edge

example :
    nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit
          (TopCat.toSSet.obj X)) L.toSingular e.edge ≫
      TopCat.localCoefficientFace L (1 : Fin 2) =
    nervePullbackCoefficientFaceHom
        (SSet.fundamentalGroupoidNerveUnit
          (TopCat.toSSet.obj X)) L.toSingular 1 e.edge ≫
      nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit
          (TopCat.toSSet.obj X)) L.toSingular
            ((TopCat.toSSet.obj X).δ 1 e.edge) :=
  nervePullbackCoefficientι_face _ _ 1 e.edge

end EdgeFaces

example (n : ℕ) :
    (TopCat.toSSet.obj X) _⦋n⦌ → ModuleCat.{max uR uX} R :=
  TopCat.localCoefficientFamily L n

example (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    TopCat.localCoefficientFamily L 0 x =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) :=
  TopCat.localCoefficientFamily_zero L x

example : SimplicialObject (ModuleCat.{max uR uX} R) :=
  TopCat.localCoefficientSimplicial L

example (n : ℕ) :
    (TopCat.localCoefficientSimplicial L).obj
        (op (SimplexCategory.mk n)) =
      TopCat.localCoefficientObj L n :=
  TopCat.localCoefficientSimplicial_obj L n

example {n : ℕ} (i : Fin (n + 2)) :
    (TopCat.localCoefficientSimplicial L).map
        (SimplexCategory.δ i).op =
      TopCat.localCoefficientFace L i :=
  TopCat.localCoefficientSimplicial_map_δ L i

example {n : ℕ} (i : Fin (n + 1)) :
    (TopCat.localCoefficientSimplicial L).map
        (SimplexCategory.σ i).op =
      TopCat.localCoefficientDegeneracy L i :=
  TopCat.localCoefficientSimplicial_map_σ L i

example : ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  TopCat.localCoefficientChainComplex L

example (n : ℕ) :
    (TopCat.localCoefficientChainComplex L).X n =
      TopCat.localCoefficientObj L n :=
  TopCat.localCoefficientChainComplex_X L n

example (n : ℕ) :
    (TopCat.localCoefficientChainComplex L).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        TopCat.localCoefficientFace L i :=
  TopCat.localCoefficientChainComplex_d L n

end Generic

section Point

variable {R : Type uR} [CommRing R]
variable (L : TopCat.LocalSystem R (TopCat.of PUnit))

example : SimplicialObject (ModuleCat.{uR} R) :=
  TopCat.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{uR} R) ℕ :=
  TopCat.localCoefficientChainComplex L

end Point

section ZeroRing

variable {X : TopCat.{uX}}
variable (L : TopCat.LocalSystem (ZMod 1) X)

example : ChainComplex (ModuleCat.{uX} (ZMod 1)) ℕ :=
  TopCat.localCoefficientChainComplex L

end ZeroRing

section IntervalEdge

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
    L.toSingular.map
        (SSet.FundamentalGroupoid.homMk intervalEdge) =
      L.map (Path.Homotopic.Quotient.mk
        ((TopCat.pathEquiv
          (TopCat.singularEdgePath intervalEdge)).cast
            (TopCat.counit_realizedVertex _)
            (TopCat.counit_realizedVertex _))) :=
  TopCat.LocalSystem.toSingular_map_homMk L intervalEdge

end IntervalEdge

section RaisedSimplexUniverse

variable (R : Type 1) [CommRing R]
variable (X : TopCat.{2}) (L : TopCat.LocalSystem R X)

example : SimplicialObject (ModuleCat.{2} R) :=
  TopCat.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{2} R) ℕ :=
  TopCat.localCoefficientChainComplex L

end RaisedSimplexUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable (X : TopCat.{1}) (L : TopCat.LocalSystem R X)

example : SimplicialObject (ModuleCat.{2} R) :=
  TopCat.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{2} R) ℕ :=
  TopCat.localCoefficientChainComplex L

end RaisedRingUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.LocalSystem.pullback

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientMap

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientHomology

#guard_msgs (error, substring := true) in
#check TopCat.constantLocalCoefficientChainIso

end StoppingBoundary

#print axioms TopCat.LocalSystem.toSingular
#print axioms TopCat.LocalSystem.toSingular_obj_mk
#print axioms TopCat.LocalSystem.toSingular_map_homMk
#print axioms TopCat.localCoefficientFamily_zero
#print axioms TopCat.localCoefficientSimplicial
#print axioms TopCat.localCoefficientSimplicial_obj
#print axioms TopCat.localCoefficientSimplicial_map_δ
#print axioms TopCat.localCoefficientSimplicial_map_σ
#print axioms TopCat.localCoefficientChainComplex
#print axioms TopCat.localCoefficientChainComplex_X
#print axioms TopCat.localCoefficientChainComplex_d

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatTests
