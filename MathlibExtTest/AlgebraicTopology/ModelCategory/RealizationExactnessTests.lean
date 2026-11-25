/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnitPiZero
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnderlyingFiniteLimits
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationFiniteConnectedFactor
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono

/-!
# Realization connectedness and exactness consumers

Persistent clients for connected cofans, the realization--singular unit,
underlying finite limits, mono pullbacks, and finite connected support.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizationExactnessTests

universe u

section ConnectedComponents

variable {J : Type u} (K : J → SSet.{u})
  [∀ j, SSet.IsConnected (K j)]

example (c : Cofan K) (hc : IsColimit c) :
    IsColimit (SSet.π₀Functor.mapCocone c) :=
  SSet.π₀.isColimitMapCoconeOfConnected K c hc

example (X : SSet.{u}) [SSet.IsConnected X] :
    Function.Bijective
      (SSet.mapπ₀ (sSetTopAdj.unit.app X)) :=
  SSet.bijective_mapπ₀_sSetTopAdj_unit_app_of_isConnected X

example (X : SSet.{u}) :
    Function.Bijective
      (SSet.mapπ₀ (sSetTopAdj.unit.app X)) :=
  SSet.bijective_mapπ₀_sSetTopAdj_unit_app X

end ConnectedComponents

section UnderlyingFiniteLimits

example :
    IsCofiltered
      (SimplexCategory.toTop.{u} ⋙ forget TopCat.{u}).Elements :=
  inferInstance

example :
    PreservesFiniteLimits
      (SSet.toTop.{u} ⋙ forget TopCat.{u}) :=
  inferInstance

variable {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

example :
    PreservesLimit (cospan f g)
      (SSet.toTop.{u} ⋙ forget TopCat.{u}) :=
  inferInstance

end UnderlyingFiniteLimits

section MonoPullbacks

variable {P X₁ X₂ S : SSet.{u}}
  {fst : P ⟶ X₁} {snd : P ⟶ X₂}
  {i : X₁ ⟶ S} {p : X₂ ⟶ S} [Mono i]

example : PreservesLimit (cospan i p) SSet.toTop :=
  inferInstance

example (sq : IsPullback fst snd i p) :
    IsPullback (SSet.toTop.map fst) (SSet.toTop.map snd)
      (SSet.toTop.map i) (SSet.toTop.map p) :=
  sq.map_toTop_of_mono

end MonoPullbacks

section FiniteConnectedFactor

section Symbolic

variable {X : SSet.{u}} {K : TopCat.{u}}
  [CompactSpace K] [PathConnectedSpace K]

example (f : K ⟶ SSet.toTop.obj X) :
    ∃ (Y : SSet.{u}) (_ : Y.Finite) (_ : Y.IsConnected)
      (i : Y ⟶ X) (_ : Mono i) (g : K ⟶ SSet.toTop.obj Y),
      f = g ≫ SSet.toTop.map i :=
  SSet.exists_factor_thru_finite_connected_of_topCatHom f

example (f : K ⟶ SSet.toTop.obj X) : True := by
  fail_if_success
    let _ : X.IsConnected := inferInstance
  have _ := SSet.exists_factor_thru_finite_connected_of_topCatHom f
  trivial

end Symbolic

section UniverseOne

variable {X : SSet.{1}} {K : TopCat.{1}}
  [CompactSpace K] [PathConnectedSpace K]

example (f : K ⟶ SSet.toTop.obj X) :
    ∃ (Y : SSet.{1}) (_ : Y.Finite) (_ : Y.IsConnected)
      (i : Y ⟶ X) (_ : Mono i) (g : K ⟶ SSet.toTop.obj Y),
      f = g ≫ SSet.toTop.map i :=
  SSet.exists_factor_thru_finite_connected_of_topCatHom f

end UniverseOne

section UniverseZero

variable {X : SSet.{0}} {K : TopCat.{0}}
  [CompactSpace K] [PathConnectedSpace K]

example (f : K ⟶ SSet.toTop.obj X) :
    ∃ (Y : SSet.{0}) (_ : Y.Finite) (_ : Y.IsConnected)
      (i : Y ⟶ X) (_ : Mono i) (g : K ⟶ SSet.toTop.obj Y),
      f = g ≫ SSet.toTop.map i :=
  SSet.exists_factor_thru_finite_connected_of_topCatHom f

end UniverseZero

section EmptyTarget

variable {K : TopCat.{u}} [CompactSpace K] [PathConnectedSpace K]

example (f : K ⟶ SSet.toTop.obj (⊥_ SSet.{u})) :
    ∃ (Y : SSet.{u}) (_ : Y.Finite) (_ : Y.IsConnected)
      (i : Y ⟶ (⊥_ SSet.{u})) (_ : Mono i)
      (g : K ⟶ SSet.toTop.obj Y),
      f = g ≫ SSet.toTop.map i :=
  SSet.exists_factor_thru_finite_connected_of_topCatHom f

end EmptyTarget

section MissingSourceHypotheses

variable {X : SSet.{u}} {K : TopCat.{u}}

example [CompactSpace K] (_f : K ⟶ SSet.toTop.obj X) : True := by
  fail_if_success
    have _ := SSet.exists_factor_thru_finite_connected_of_topCatHom _f
  trivial

example [PathConnectedSpace K] (_f : K ⟶ SSet.toTop.obj X) : True := by
  fail_if_success
    have _ := SSet.exists_factor_thru_finite_connected_of_topCatHom _f
  trivial

end MissingSourceHypotheses

end FiniteConnectedFactor
end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizationExactnessTests
