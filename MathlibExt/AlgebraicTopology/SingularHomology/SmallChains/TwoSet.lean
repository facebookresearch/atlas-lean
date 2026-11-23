/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains
public import MathlibExt.Topology.Category.TopCat.OrderedTwoSetCover
public import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Pushouts of small chains for two sets

Constructs the subordinate singular complexes for two sets, their intersection
and their combined small cover. The square induces a functorial pushout of chain
complexes and an isomorphism between the associated cokernels.
-/

@[expose] public section

open CategoryTheory Limits Simplicial TopCat SSet

namespace AlgebraicTopology

universe w v u

variable {X : TopCat.{w}}

noncomputable def subCxInter (A B : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  subordinateCover (smallCoverInter A B)
noncomputable def subCxLeft (A : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  subordinateCover (smallCoverLeft A)
noncomputable def subCxRight (B : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  subordinateCover (smallCoverRight B)
noncomputable def subCxBoth (A B : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  subordinateCover (smallCoverBoth A B)

lemma subCxLeft_eq (A : Set X) : subCxLeft A = subordinateSet A := by
  dsimp [subCxLeft, smallCoverLeft, subordinateCover]
  simp
lemma subCxRight_eq (B : Set X) : subCxRight B = subordinateSet B := by
  dsimp [subCxRight, smallCoverRight, subordinateCover]
  simp
lemma subCxInter_eq (A B : Set X) : subCxInter A B = subordinateSet (A ∩ B) := by
  dsimp [subCxInter, smallCoverInter, subordinateCover]
  simp
lemma subCxBoth_eq_sup (A B : Set X) :
    subCxBoth A B = subordinateSet A ⊔ subordinateSet B := by
  dsimp [subCxBoth, smallCoverBoth, subordinateCover]
  rw [iSup_bool_eq]
  simp
lemma subCxInter_le_left (A B : Set X) : subCxInter A B ≤ subCxLeft A := by
  rw [subCxInter_eq, subCxLeft_eq]
  exact subordinateSet_mono Set.inter_subset_left
lemma subCxInter_le_right (A B : Set X) : subCxInter A B ≤ subCxRight B := by
  rw [subCxInter_eq, subCxRight_eq]
  exact subordinateSet_mono Set.inter_subset_right
lemma subCxLeft_le_both (A B : Set X) : subCxLeft A ≤ subCxBoth A B := by
  rw [subCxLeft_eq, subCxBoth_eq_sup]
  exact le_sup_left
lemma subCxRight_le_both (A B : Set X) : subCxRight B ≤ subCxBoth A B := by
  rw [subCxRight_eq, subCxBoth_eq_sup]
  exact le_sup_right
lemma sup_left_right_eq_both (A B : Set X) :
    subCxLeft A ⊔ subCxRight B = subCxBoth A B := by
  rw [subCxLeft_eq, subCxRight_eq, subCxBoth_eq_sup]
lemma inf_left_right_eq_inter (A B : Set X) :
    subCxLeft A ⊓ subCxRight B = subCxInter A B := by
  rw [subCxLeft_eq, subCxRight_eq, subCxInter_eq, subordinateSet_inter]

theorem bicartTwoSet (A B : Set X) :
    SSet.Subcomplex.BicartSq (subCxInter A B) (subCxLeft A) (subCxRight B) (subCxBoth A B) where
  sup_eq := sup_left_right_eq_both A B
  inf_eq := by rw [inf_left_right_eq_inter]

theorem sSetPushoutTwoSet (A B : Set X) :
    IsPushout (SSet.Subcomplex.homOfLE (subCxInter_le_left A B))
      (SSet.Subcomplex.homOfLE (subCxInter_le_right A B))
      (SSet.Subcomplex.homOfLE (subCxLeft_le_both A B))
      (SSet.Subcomplex.homOfLE (subCxRight_le_both A B)) :=
  SSet.Subcomplex.BicartSq.isPushout (bicartTwoSet A B)

section ChainTwoSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

noncomputable abbrev chainInter (A B : Set X) (R : C) :
    ChainComplex C ℕ :=
  smallChainComplex R (smallCoverInter A B)
noncomputable abbrev chainLeft (A : Set X) (R : C) :
    ChainComplex C ℕ :=
  smallChainComplex R (smallCoverLeft A)
noncomputable abbrev chainRight (B : Set X) (R : C) :
    ChainComplex C ℕ :=
  smallChainComplex R (smallCoverRight B)
noncomputable abbrev chainBoth (A B : Set X) (R : C) :
    ChainComplex C ℕ :=
  smallChainComplex R (smallCoverBoth A B)

noncomputable def mapInterLeft (A B : Set X) (R : C) :
    chainInter A B R ⟶ chainLeft A R :=
  smallChainMapOfLE R _ _ (subCxInter_le_left A B)
noncomputable def mapInterRight (A B : Set X) (R : C) :
    chainInter A B R ⟶ chainRight B R :=
  smallChainMapOfLE R _ _ (subCxInter_le_right A B)
noncomputable def mapLeftBoth (A B : Set X) (R : C) :
    chainLeft A R ⟶ chainBoth A B R :=
  smallChainMapOfLE R _ _ (subCxLeft_le_both A B)
noncomputable def mapRightBoth (A B : Set X) (R : C) :
    chainRight B R ⟶ chainBoth A B R :=
  smallChainMapOfLE R _ _ (subCxRight_le_both A B)

section CoverFunctorial

variable (R : C)

/-- Induced chain map on the intersection small-chain complex for a morphism of
ordered two-set covers. Built from `smallChainMapOfMapsTo` via `interMaps`. -/
noncomputable def chainInterMap {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    chainInter C'.left C'.right R ⟶ chainInter D.left D.right R :=
  smallChainMapOfMapsTo R f.f
    (smallCoverInter C'.left C'.right) (smallCoverInter D.left D.right)
    (fun _ => ⟨(), OrderedTwoSetCover.interMaps f⟩)

/-- Induced chain map on the left small-chain complex. -/
noncomputable def chainLeftMap {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    chainLeft C'.left R ⟶ chainLeft D.left R :=
  smallChainMapOfMapsTo R f.f
    (smallCoverLeft C'.left) (smallCoverLeft D.left)
    (fun _ => ⟨(), f.left_maps⟩)

/-- Induced chain map on the right small-chain complex. -/
noncomputable def chainRightMap {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    chainRight C'.right R ⟶ chainRight D.right R :=
  smallChainMapOfMapsTo R f.f
    (smallCoverRight C'.right) (smallCoverRight D.right)
    (fun _ => ⟨(), f.right_maps⟩)

/-- Induced chain map on the both-cover small-chain complex. Preserves the
`Bool` side canonically: `true` (left) stays `true`, `false` (right) stays `false`. -/
noncomputable def chainBothMap {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    chainBoth C'.left C'.right R ⟶ chainBoth D.left D.right R :=
  smallChainMapOfMapsTo R f.f
    (smallCoverBoth C'.left C'.right) (smallCoverBoth D.left D.right)
    (fun b => ⟨b, by
      cases b
      · exact f.right_maps
      · exact f.left_maps⟩)

@[simp]
lemma chainInterMap_id (C' : OrderedTwoSetCover.{w}) :
    chainInterMap R (𝟙 C') = 𝟙 _ := by
  dsimp [chainInterMap, smallChainMapOfMapsTo]
  exact smallChainMapOfImageLE_id_aux R _ _

@[simp]
lemma chainLeftMap_id (C' : OrderedTwoSetCover.{w}) :
    chainLeftMap R (𝟙 C') = 𝟙 _ := by
  dsimp [chainLeftMap, smallChainMapOfMapsTo]
  exact smallChainMapOfImageLE_id_aux R _ _

@[simp]
lemma chainRightMap_id (C' : OrderedTwoSetCover.{w}) :
    chainRightMap R (𝟙 C') = 𝟙 _ := by
  dsimp [chainRightMap, smallChainMapOfMapsTo]
  exact smallChainMapOfImageLE_id_aux R _ _

@[simp]
lemma chainBothMap_id (C' : OrderedTwoSetCover.{w}) :
    chainBothMap R (𝟙 C') = 𝟙 _ := by
  dsimp [chainBothMap, smallChainMapOfMapsTo]
  exact smallChainMapOfImageLE_id_aux R _ _

lemma chainInterMap_comp {C' D E : OrderedTwoSetCover.{w}} (f : C' ⟶ D) (g : D ⟶ E) :
    chainInterMap R (f ≫ g) = chainInterMap R f ≫ chainInterMap R g := by
  dsimp [chainInterMap, smallChainMapOfMapsTo]
  rw [smallChainMapOfImageLE_comp]
  rfl

lemma chainLeftMap_comp {C' D E : OrderedTwoSetCover.{w}} (f : C' ⟶ D) (g : D ⟶ E) :
    chainLeftMap R (f ≫ g) = chainLeftMap R f ≫ chainLeftMap R g := by
  dsimp [chainLeftMap, smallChainMapOfMapsTo]
  rw [smallChainMapOfImageLE_comp]
  rfl

lemma chainRightMap_comp {C' D E : OrderedTwoSetCover.{w}} (f : C' ⟶ D) (g : D ⟶ E) :
    chainRightMap R (f ≫ g) = chainRightMap R f ≫ chainRightMap R g := by
  dsimp [chainRightMap, smallChainMapOfMapsTo]
  rw [smallChainMapOfImageLE_comp]
  rfl

lemma chainBothMap_comp {C' D E : OrderedTwoSetCover.{w}} (f : C' ⟶ D) (g : D ⟶ E) :
    chainBothMap R (f ≫ g) = chainBothMap R f ≫ chainBothMap R g := by
  dsimp [chainBothMap, smallChainMapOfMapsTo]
  rw [smallChainMapOfImageLE_comp]
  rfl

/-- Naturality of `mapInterLeft` with respect to cover morphisms. Categorical proof via mono. -/
lemma chainInterMap_naturality_left {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    mapInterLeft C'.left C'.right R ≫ chainLeftMap R f =
      chainInterMap R f ≫ mapInterLeft D.left D.right R := by
  apply (cancel_mono (smallChainInclusion R (smallCoverLeft D.left))).mp
  have h_left : chainLeftMap R f ≫ smallChainInclusion R (smallCoverLeft D.left) =
      smallChainInclusion R (smallCoverLeft C'.left) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_inter : chainInterMap R f ≫ smallChainInclusion R (smallCoverInter D.left D.right) =
      smallChainInclusion R (smallCoverInter C'.left C'.right) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_map_left_C : mapInterLeft C'.left C'.right R ≫
      smallChainInclusion R (smallCoverLeft C'.left) =
      smallChainInclusion R (smallCoverInter C'.left C'.right) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h_map_left_D : mapInterLeft D.left D.right R ≫
      smallChainInclusion R (smallCoverLeft D.left) =
      smallChainInclusion R (smallCoverInter D.left D.right) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  calc (mapInterLeft C'.left C'.right R ≫ chainLeftMap R f) ≫
        smallChainInclusion R (smallCoverLeft D.left)
      = mapInterLeft C'.left C'.right R ≫
          (chainLeftMap R f ≫ smallChainInclusion R (smallCoverLeft D.left)) := by
        rw [Category.assoc]
    _ = mapInterLeft C'.left C'.right R ≫
          (smallChainInclusion R (smallCoverLeft C'.left) ≫ singularChainMap R f.f) := by
        rw [h_left]
    _ = (mapInterLeft C'.left C'.right R ≫
          smallChainInclusion R (smallCoverLeft C'.left)) ≫ singularChainMap R f.f := by
        rw [Category.assoc]
    _ = smallChainInclusion R (smallCoverInter C'.left C'.right) ≫
          singularChainMap R f.f := by
        rw [h_map_left_C]
    _ = chainInterMap R f ≫ smallChainInclusion R (smallCoverInter D.left D.right) := by
        rw [← h_inter]
    _ = chainInterMap R f ≫
          (mapInterLeft D.left D.right R ≫ smallChainInclusion R (smallCoverLeft D.left)) := by
        rw [h_map_left_D]
    _ = (chainInterMap R f ≫ mapInterLeft D.left D.right R) ≫
          smallChainInclusion R (smallCoverLeft D.left) := by
        rw [Category.assoc]

/-- Naturality of `mapInterRight`. -/
lemma chainInterMap_naturality_right {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    mapInterRight C'.left C'.right R ≫ chainRightMap R f =
      chainInterMap R f ≫ mapInterRight D.left D.right R := by
  apply (cancel_mono (smallChainInclusion R (smallCoverRight D.right))).mp
  have h_right : chainRightMap R f ≫ smallChainInclusion R (smallCoverRight D.right) =
      smallChainInclusion R (smallCoverRight C'.right) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_inter : chainInterMap R f ≫ smallChainInclusion R (smallCoverInter D.left D.right) =
      smallChainInclusion R (smallCoverInter C'.left C'.right) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_map_right_C : mapInterRight C'.left C'.right R ≫
      smallChainInclusion R (smallCoverRight C'.right) =
      smallChainInclusion R (smallCoverInter C'.left C'.right) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h_map_right_D : mapInterRight D.left D.right R ≫
      smallChainInclusion R (smallCoverRight D.right) =
      smallChainInclusion R (smallCoverInter D.left D.right) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  calc (mapInterRight C'.left C'.right R ≫ chainRightMap R f) ≫
        smallChainInclusion R (smallCoverRight D.right)
      = mapInterRight C'.left C'.right R ≫
          (chainRightMap R f ≫ smallChainInclusion R (smallCoverRight D.right)) := by
        rw [Category.assoc]
    _ = mapInterRight C'.left C'.right R ≫
          (smallChainInclusion R (smallCoverRight C'.right) ≫ singularChainMap R f.f) := by
        rw [h_right]
    _ = (mapInterRight C'.left C'.right R ≫
          smallChainInclusion R (smallCoverRight C'.right)) ≫ singularChainMap R f.f := by
        rw [Category.assoc]
    _ = smallChainInclusion R (smallCoverInter C'.left C'.right) ≫
          singularChainMap R f.f := by
        rw [h_map_right_C]
    _ = chainInterMap R f ≫ smallChainInclusion R (smallCoverInter D.left D.right) := by
        rw [← h_inter]
    _ = chainInterMap R f ≫
          (mapInterRight D.left D.right R ≫ smallChainInclusion R (smallCoverRight D.right)) := by
        rw [h_map_right_D]
    _ = (chainInterMap R f ≫ mapInterRight D.left D.right R) ≫
          smallChainInclusion R (smallCoverRight D.right) := by
        rw [Category.assoc]

/-- Naturality of `mapLeftBoth`. -/
lemma chainLeftMap_naturality_both {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    mapLeftBoth C'.left C'.right R ≫ chainBothMap R f =
      chainLeftMap R f ≫ mapLeftBoth D.left D.right R := by
  apply (cancel_mono (smallChainInclusion R (smallCoverBoth D.left D.right))).mp
  have h_left : chainLeftMap R f ≫ smallChainInclusion R (smallCoverLeft D.left) =
      smallChainInclusion R (smallCoverLeft C'.left) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_both : chainBothMap R f ≫ smallChainInclusion R (smallCoverBoth D.left D.right) =
      smallChainInclusion R (smallCoverBoth C'.left C'.right) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_map_left_C : mapLeftBoth C'.left C'.right R ≫
      smallChainInclusion R (smallCoverBoth C'.left C'.right) =
      smallChainInclusion R (smallCoverLeft C'.left) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h_map_left_D : mapLeftBoth D.left D.right R ≫
      smallChainInclusion R (smallCoverBoth D.left D.right) =
      smallChainInclusion R (smallCoverLeft D.left) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  calc (mapLeftBoth C'.left C'.right R ≫ chainBothMap R f) ≫
        smallChainInclusion R (smallCoverBoth D.left D.right)
      = mapLeftBoth C'.left C'.right R ≫
          (chainBothMap R f ≫ smallChainInclusion R (smallCoverBoth D.left D.right)) := by
        rw [Category.assoc]
    _ = mapLeftBoth C'.left C'.right R ≫
          (smallChainInclusion R (smallCoverBoth C'.left C'.right) ≫ singularChainMap R f.f) := by
        rw [h_both]
    _ = (mapLeftBoth C'.left C'.right R ≫
          smallChainInclusion R (smallCoverBoth C'.left C'.right)) ≫ singularChainMap R f.f := by
        rw [Category.assoc]
    _ = smallChainInclusion R (smallCoverLeft C'.left) ≫ singularChainMap R f.f := by
        rw [h_map_left_C]
    _ = chainLeftMap R f ≫ smallChainInclusion R (smallCoverLeft D.left) := by
        rw [← h_left]
    _ = chainLeftMap R f ≫
          (mapLeftBoth D.left D.right R ≫
            smallChainInclusion R (smallCoverBoth D.left D.right)) := by
        rw [h_map_left_D]
    _ = (chainLeftMap R f ≫ mapLeftBoth D.left D.right R) ≫
          smallChainInclusion R (smallCoverBoth D.left D.right) := by
        rw [Category.assoc]

/-- Naturality of `mapRightBoth`. -/
lemma chainRightMap_naturality_both {C' D : OrderedTwoSetCover.{w}} (f : C' ⟶ D) :
    mapRightBoth C'.left C'.right R ≫ chainBothMap R f =
      chainRightMap R f ≫ mapRightBoth D.left D.right R := by
  apply (cancel_mono (smallChainInclusion R (smallCoverBoth D.left D.right))).mp
  have h_right : chainRightMap R f ≫ smallChainInclusion R (smallCoverRight D.right) =
      smallChainInclusion R (smallCoverRight C'.right) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_both : chainBothMap R f ≫ smallChainInclusion R (smallCoverBoth D.left D.right) =
      smallChainInclusion R (smallCoverBoth C'.left C'.right) ≫ singularChainMap R f.f :=
    smallChainMapOfMapsTo_comp_inclusion R f.f _ _ _
  have h_map_right_C : mapRightBoth C'.left C'.right R ≫
      smallChainInclusion R (smallCoverBoth C'.left C'.right) =
      smallChainInclusion R (smallCoverRight C'.right) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h_map_right_D : mapRightBoth D.left D.right R ≫
      smallChainInclusion R (smallCoverBoth D.left D.right) =
      smallChainInclusion R (smallCoverRight D.right) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  calc (mapRightBoth C'.left C'.right R ≫ chainBothMap R f) ≫
        smallChainInclusion R (smallCoverBoth D.left D.right)
      = mapRightBoth C'.left C'.right R ≫
          (chainBothMap R f ≫ smallChainInclusion R (smallCoverBoth D.left D.right)) := by
        rw [Category.assoc]
    _ = mapRightBoth C'.left C'.right R ≫
          (smallChainInclusion R (smallCoverBoth C'.left C'.right) ≫ singularChainMap R f.f) := by
        rw [h_both]
    _ = (mapRightBoth C'.left C'.right R ≫
          smallChainInclusion R (smallCoverBoth C'.left C'.right)) ≫ singularChainMap R f.f := by
        rw [Category.assoc]
    _ = smallChainInclusion R (smallCoverRight C'.right) ≫ singularChainMap R f.f := by
        rw [h_map_right_C]
    _ = chainRightMap R f ≫ smallChainInclusion R (smallCoverRight D.right) := by
        rw [← h_right]
    _ = chainRightMap R f ≫
          (mapRightBoth D.left D.right R ≫
            smallChainInclusion R (smallCoverBoth D.left D.right)) := by
        rw [h_map_right_D]
    _ = (chainRightMap R f ≫ mapRightBoth D.left D.right R) ≫
          smallChainInclusion R (smallCoverBoth D.left D.right) := by
        rw [Category.assoc]

end CoverFunctorial

lemma squareTwoSet (A B : Set X) (R : C) :
    mapInterLeft A B R ≫ mapLeftBoth A B R = mapInterRight A B R ≫ mapRightBoth A B R := by
  have h_left_both : mapLeftBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B) =
      smallChainInclusion R (smallCoverLeft A) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h_inter_left : mapInterLeft A B R ≫ smallChainInclusion R (smallCoverLeft A) =
      smallChainInclusion R (smallCoverInter A B) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h1 : mapInterLeft A B R ≫ mapLeftBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B) =
      smallChainInclusion R (smallCoverInter A B) := by
    calc mapInterLeft A B R ≫ mapLeftBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B)
        = mapInterLeft A B R ≫ smallChainInclusion R (smallCoverLeft A) := by
          rw [h_left_both]
      _ = smallChainInclusion R (smallCoverInter A B) := by
          rw [h_inter_left]
  have h_right_both : mapRightBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B) =
      smallChainInclusion R (smallCoverRight B) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h_inter_right : mapInterRight A B R ≫ smallChainInclusion R (smallCoverRight B) =
      smallChainInclusion R (smallCoverInter A B) :=
    smallChainMapOfLE_comp_inclusion R _ _ _
  have h2 : mapInterRight A B R ≫ mapRightBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B) =
      smallChainInclusion R (smallCoverInter A B) := by
    calc mapInterRight A B R ≫ mapRightBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B)
        = mapInterRight A B R ≫ smallChainInclusion R (smallCoverRight B) := by
          rw [h_right_both]
      _ = smallChainInclusion R (smallCoverInter A B) := by
          rw [h_inter_right]
  have heq : (mapInterLeft A B R ≫ mapLeftBoth A B R) ≫ smallChainInclusion R (smallCoverBoth A B) =
      (mapInterRight A B R ≫ mapRightBoth A B R) ≫ smallChainInclusion R (smallCoverBoth A B) := by
    calc (mapInterLeft A B R ≫ mapLeftBoth A B R) ≫ smallChainInclusion R (smallCoverBoth A B)
        = mapInterLeft A B R ≫ mapLeftBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B) := by
          rw [Category.assoc]
      _ = smallChainInclusion R (smallCoverInter A B) := by
          rw [h1]
      _ = mapInterRight A B R ≫ mapRightBoth A B R ≫
          smallChainInclusion R (smallCoverBoth A B) := by
          rw [← h2]
      _ = (mapInterRight A B R ≫ mapRightBoth A B R) ≫
          smallChainInclusion R (smallCoverBoth A B) := by
          rw [Category.assoc]
  exact (cancel_mono (smallChainInclusion R (smallCoverBoth A B))).mp heq

theorem chainIsPushout (A B : Set X) (R : C) :
    IsPushout (mapInterLeft A B R) (mapInterRight A B R)
      (mapLeftBoth A B R) (mapRightBoth A B R) := by
  simpa [mapInterLeft, mapInterRight, mapLeftBoth, mapRightBoth,
    chainInter, chainLeft, chainRight, chainBoth, smallChainMapOfLE,
    smallChainComplex, subCxInter, subCxLeft, subCxRight, subCxBoth] using
    (sSetPushoutTwoSet A B).map ((SSet.chainComplexFunctor C).obj R)

end ChainTwoSet

section CokernelComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [HasCoequalizers C]

variable {X : TopCat.{w}}

noncomputable def cokernelComparison (A B : Set X) (R : C) :
    cokernel (mapInterRight (C := C) A B R) ⟶ cokernel (mapLeftBoth (C := C) A B R) :=
  cokernel.map _ _ (mapInterLeft A B R) (mapRightBoth A B R) (squareTwoSet A B R).symm

noncomputable instance isIsoCokernelComparison (A B : Set X) (R : C) :
    IsIso (cokernelComparison (C := C) A B R) := by
  have h : IsPushout (mapInterRight A B R) (mapInterLeft A B R)
      (mapRightBoth A B R) (mapLeftBoth A B R) := (chainIsPushout A B R).flip
  exact isIso_cokernel_map_of_isPushout h

end CokernelComparison

end AlgebraicTopology
