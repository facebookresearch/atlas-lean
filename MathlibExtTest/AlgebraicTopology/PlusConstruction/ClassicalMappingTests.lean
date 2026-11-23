/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalMapping

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u

#check @LoopCellIndependentPlus.original_connected_CW_plus_map_extension
#print axioms LoopCellIndependentPlus.original_connected_CW_plus_map_extension
#check @LoopCellIndependentPlus.original_subgroupPreserving_plus_map_extension
#print axioms LoopCellIndependentPlus.original_subgroupPreserving_plus_map_extension
#check @TopCat.doubleMappingCylinderOverlapHomotopyEquiv
#print axioms TopCat.doubleMappingCylinderOverlapHomotopyEquiv
#check @LoopCellIndependentPlus.originalPushoutInclusion_pi1_bijective
#print axioms LoopCellIndependentPlus.originalPushoutInclusion_pi1_bijective

-- The original overlap projection and midpoint are the literal two maps.
example {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    ∃ e : TopCat.of (TopCat.doubleMappingCylinderOverlap i f :
        Set (TopCat.doubleMappingCylinder i f)) ≃ₕ X,
      e.toFun = (TopCat.doubleMappingCylinderOverlapProjection i f).hom ∧
        e.invFun = (TopCat.doubleMappingCylinderMidpoint i f).hom := by
  let e := TopCat.doubleMappingCylinderOverlapHomotopyEquiv i f
  exact ⟨e.val, e.property⟩

-- Every actual H point is covered; H is not assumed connected or CW-type.
example (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∀ h : H, Function.Bijective (FundamentalGroup.mapOfEq
      (pushout.inr i f).hom rfl (x := h)) :=
  LoopCellIndependentPlus.originalPushoutInclusion_pi1_bijective X x P H f hkill

-- A genuine map killing P factors through the independently constructed map.
example (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∃ F : LoopCellRegularThreeComparison.originalThree X x P ⟶ H,
      i ≫ F = f ∧
        Nonempty (ContinuousMap.HomotopyRel (i ≫ F).hom f.hom Set.univ) := by
  obtain ⟨r, F, hFr, hF, hr, htriangle, hleft, hright, hUnique⟩ :=
    LoopCellIndependentPlus.original_connected_CW_plus_map_extension X x P H f hkill
  exact ⟨F, hF, htriangle⟩

-- BOTH inverse families refer to the actual pushout retraction and whole H.
example (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let j := pushout.inr i f
    ∃ r : pushout i f ⟶ H, j ≫ r = 𝟙 H ∧
      Nonempty (ContinuousMap.HomotopyRel (j ≫ r).hom (𝟙 H : H ⟶ H).hom Set.univ) ∧
        Nonempty (ContinuousMap.HomotopyRel (r ≫ j).hom
          (𝟙 (pushout i f) : (pushout i f : TopCat.{u}) ⟶ (pushout i f : TopCat.{u})).hom
          (Set.range j)) := by
  obtain ⟨r, F, hFr, hF, hr, htriangle, hleft, hright, hUnique⟩ :=
    LoopCellIndependentPlus.original_connected_CW_plus_map_extension X x P H f hkill
  exact ⟨r, hr, hleft, hright⟩

-- Relative uniqueness gives both directions at EVERY original source point.
example (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∃ F : LoopCellRegularThreeComparison.originalThree X x P ⟶ H,
      i ≫ F = f ∧ ∀ G, i ≫ G = f →
        ∃ K : ContinuousMap.HomotopyRel F.hom G.hom (Set.range i),
          ∀ t : unitInterval, ∀ z : X, K (t, i z) = F (i z) := by
  obtain ⟨r, F, hFr, hF, hr, htriangle, hleft, hright, hUnique⟩ :=
    LoopCellIndependentPlus.original_connected_CW_plus_map_extension X x P H f hkill
  refine ⟨F, hF, ?_⟩
  intro G hG
  obtain ⟨K⟩ := (hUnique G hG).1
  exact ⟨K, fun t z => K.eq_fst t ⟨z, rfl⟩⟩

-- The selected subgroup condition uses the actual map and selected points.
example (X Y : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    [ConnectedSpace Y] (x : X) (y : Y) (f : X ⟶ Y) (hxy : f x = y)
    (P : Subgroup (FundamentalGroup X x)) (Q : Subgroup (FundamentalGroup Y y))
    [P.Normal] [Group.IsPerfect P] [Q.Normal] [Group.IsPerfect Q]
    (hPQ : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom hxy p ∈ Q) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    letI : PathConnectedSpace Y :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl Y)
    let iX := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let iY := LoopCellAttachment.inclusion Y y Q ≫
      LoopCellRegularThreeComparison.originalThreeInclusion Y y Q
    ∃ F : LoopCellRegularThreeComparison.originalThree X x P ⟶
        LoopCellRegularThreeComparison.originalThree Y y Q,
      iX ≫ F = f ≫ iY ∧
        Nonempty (ContinuousMap.HomotopyRel (iX ≫ F).hom (f ≫ iY).hom Set.univ) := by
  obtain ⟨F, hF, htriangle, hUnique⟩ :=
    LoopCellIndependentPlus.original_subgroupPreserving_plus_map_extension X Y x y f hxy P Q hPQ
  exact ⟨F, hF, htriangle⟩

end
