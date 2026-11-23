/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalMappingGeometry

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped TopCat.modelCategory ContinuousMap

universe u

#check @LoopCellIndependentPlus.originalInclusion_groupoid_full_essSurj
#print axioms LoopCellIndependentPlus.originalInclusion_groupoid_full_essSurj
#check @LoopCellIndependentPlus.originalInclusion_basedFunctor_end_desc
#print axioms LoopCellIndependentPlus.originalInclusion_basedFunctor_end_desc
#check @TopCat.pathEvalZero_trivialFibration
#print axioms TopCat.pathEvalZero_trivialFibration
#check @TopCat.exists_homotopyExtension_of_cofibration
#print axioms TopCat.exists_homotopyExtension_of_cofibration
#check @TopCat.exists_extension_of_trivialCofibration
#print axioms TopCat.exists_extension_of_trivialCofibration
#check @TopCat.homotopyRel_of_trivialCofibration
#print axioms TopCat.homotopyRel_of_trivialCofibration
#check @TopCat.exists_pushout_extension_of_trivialCofibration
#print axioms TopCat.exists_pushout_extension_of_trivialCofibration
#check @LoopCellIndependentPlus.originalInclusion_cofibration
#print axioms LoopCellIndependentPlus.originalInclusion_cofibration
#check @LoopCellIndependentPlus.subgroupPreserving_composite_kills
#print axioms LoopCellIndependentPlus.subgroupPreserving_composite_kills

-- Every actual target is allowed; no target CW/connectedness premise.
example {A B H : TopCat.{u}} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j]
    (f : A ⟶ H) : ∃ g : B ⟶ H, j ≫ g = f :=
  TopCat.exists_extension_of_trivialCofibration j f

-- The whole image is fixed at every time, not merely at one chosen point.
example {A B H : TopCat.{u}} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j]
    (f g : B ⟶ H) (h : j ≫ f = j ≫ g) :
    ∃ K : ContinuousMap.HomotopyRel f.hom g.hom (Set.range j),
      ∀ t : unitInterval, ∀ a : A, K (t, j a) = f (j a) := by
  obtain ⟨K⟩ := TopCat.homotopyRel_of_trivialCofibration j f g h
  exact ⟨K, fun t a => K.eq_fst t ⟨a, rfl⟩⟩

-- The same actual pushout gives the strict source triangle and relative comparison.
example {X A H : TopCat.{u}} (i : X ⟶ A) (f : X ⟶ H)
    [Cofibration (pushout.inr i f)] [WeakEquivalence (pushout.inr i f)] :
    ∃ F : A ⟶ H, i ≫ F = f ∧
      ∀ G : A ⟶ H, i ≫ G = f →
        Nonempty (ContinuousMap.HomotopyRel F.hom G.hom (Set.range i)) :=
  TopCat.exists_pushout_extension_of_trivialCofibration i f

-- The genuine original cell composite supplies its own cofibration.
example (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    Cofibration (LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P) :=
  LoopCellIndependentPlus.originalInclusion_cofibration X x P

-- Preservation of the selected subgroup is evaluated at the actual image point.
example (X Y : TopCat.{u}) [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    [ConnectedSpace Y] (x : X) (y : Y) (f : X ⟶ Y) (hxy : f x = y)
    (P : Subgroup (FundamentalGroup X x)) (Q : Subgroup (FundamentalGroup Y y))
    [Q.Normal] [Group.IsPerfect Q]
    (hPQ : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom hxy p ∈ Q) :
    letI : PathConnectedSpace Y :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl Y)
    let i := LoopCellAttachment.inclusion Y y Q ≫
      LoopCellRegularThreeComparison.originalThreeInclusion Y y Q
    P ≤ MonoidHom.ker (FundamentalGroup.mapOfEq (f ≫ i).hom (congrArg i hxy)) :=
  LoopCellIndependentPlus.subgroupPreserving_composite_kills X Y x y f hxy P Q hPQ

-- A prescribed original source homotopy is extended pointwise at ALL times.
example {A B H : TopCat.{u}} (i : A ⟶ B) [Cofibration i]
    (f : B ⟶ H) (g : A ⟶ H) (K : TopCat.Homotopy (i ≫ f) g) :
    ∃ gB : B ⟶ H, ∃ L : TopCat.Homotopy f gB,
      i ≫ gB = g ∧ ∀ t : unitInterval, ∀ a : A, L (t, i a) = K (t, a) :=
  TopCat.exists_homotopyExtension_of_cofibration i f g K

-- Fullness and essential surjectivity concern the SAME ordinary plus map.
example (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    (FundamentalGroupoid.map i.hom).Full ∧ (FundamentalGroupoid.map i.hom).EssSurj :=
  LoopCellIndependentPlus.originalInclusion_groupoid_full_essSurj X x P

-- Each actual target point is allowed, including arbitrary target components.
example (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) (h : H) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let Z := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let B := Groupoid.basedFunctor (FundamentalGroupoid.mk h)
      (MonoidHom.id (FundamentalGroup H h))
    ∃ F : FundamentalGroupoid Z ⥤ SingleObj (FundamentalGroup H h),
      ∀ q : FundamentalGroup X x,
        ((FundamentalGroupoid.map i.hom ⋙ F).map q.asHom : FundamentalGroup H h) =
          ((FundamentalGroupoid.map f.hom ⋙ B).map q.asHom : FundamentalGroup H h) :=
  LoopCellIndependentPlus.originalInclusion_basedFunctor_end_desc X x P H f hkill h

end
