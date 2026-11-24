/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Small chains as subcomplexes of the singular simplicial set

Primary API uses `SSet.Subcomplex` to model chains subordinate to a cover.

- `subordinateSet A` : simplices with image in `A`
- `subordinateCover U` : sup of `subordinateSet (U i)` for cover `U`
- `smallChainComplex C R U` : chains of `subordinateCover U`
- `smallChainInclusion C R U` : inclusion into singular chains of `X`
- `smallChainMapOfLE` : refinement via `homOfLE`

## Main definitions
* `subordinateSet`
* `subordinateCover`
* `smallChainComplex`
* `smallChainInclusion`
* `smallChainMapOfLE`
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

namespace AlgebraicTopology

universe w v u

section SmallChainsTop

variable {X : TopCat.{w}}

/-- Singular simplices whose image is contained in `A`. -/
noncomputable def subordinateSet (A : Set X) :
    (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | Set.range (X.toSSetObjEquiv n σ) ⊆ A}
  map f σ hσ := by
    rintro _ ⟨z, rfl⟩
    rw [← Quiver.Hom.op_unop f]
    rw [TopCat.toSSetObjEquiv_naturality_apply]
    exact hσ ⟨Convexity.StdSimplex.map f.unop z, rfl⟩

lemma subordinateSet_mono {A B : Set X} (h : A ⊆ B) :
    subordinateSet A ≤ subordinateSet B := by
  intro n σ hσ
  exact hσ.trans h

@[simp]
lemma subordinateSet_inter (A B : Set X) :
    subordinateSet (A ∩ B) = subordinateSet A ⊓ subordinateSet B := by
  ext n σ
  simp only [subordinateSet, Subfunctor.min_obj, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun _ hx ↦ (h hx).1, fun _ hx ↦ (h hx).2⟩
  · rintro ⟨hA, hB⟩ _ hx
    exact ⟨hA hx, hB hx⟩

/-- The union, in the subcomplex lattice, of simplices subordinate to one cover member. -/
noncomputable def subordinateCover {ι : Type*} (U : ι → Set X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  ⨆ i, subordinateSet (U i)

@[simp]
lemma subordinateCover_singleton (A : Set X) :
    subordinateCover (fun _ : Unit => A) = subordinateSet A := by
  simp [subordinateCover]

lemma subordinateCover_mono {ι κ : Type*} {U : ι → Set X} {V : κ → Set X}
    (h : ∀ i, ∃ j, U i ⊆ V j) :
    subordinateCover U ≤ subordinateCover V := by
  apply iSup_le
  intro i
  obtain ⟨j, hj⟩ := h i
  calc subordinateSet (U i) ≤ subordinateSet (V j) := subordinateSet_mono hj
    _ ≤ subordinateCover V := le_iSup (fun k => subordinateSet (V k)) j

lemma subordinateSet_image_le {Y : TopCat.{w}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    (subordinateSet A).image (TopCat.toSSet.map f) ≤ subordinateSet (X := Y) B := by
  rw [SSet.Subcomplex.image_le_iff]
  intro n σ hσ
  change Set.range (Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ)) ⊆ B
  have eq : Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ) =
      f.hom.comp (X.toSSetObjEquiv n σ) := rfl
  rw [eq]
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  have hg : (X.toSSetObjEquiv n σ) z ∈ A := hσ ⟨z, rfl⟩
  exact h hg

lemma subordinateSet_preimage {Y : TopCat.{w}} (f : X ⟶ Y) (B : Set Y) :
    (subordinateSet (X := Y) B).preimage (TopCat.toSSet.map f) = subordinateSet (f ⁻¹' B) := by
  ext n σ
  simp only [SSet.Subcomplex.preimage_obj, subordinateSet, Set.mem_preimage,
    Set.mem_ofPred_eq]
  have eq : Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ) =
      f.hom.comp (X.toSSetObjEquiv n σ) := rfl
  rw [eq]
  constructor
  · intro h y hy
    obtain ⟨z, rfl⟩ := hy
    have hy' : f ((X.toSSetObjEquiv n σ) z) ∈ B := h ⟨_, rfl⟩
    exact hy'
  · intro h y hy
    obtain ⟨z, rfl⟩ := hy
    have hz : (X.toSSetObjEquiv n σ) z ∈ f ⁻¹' B := h ⟨z, rfl⟩
    exact hz

lemma subordinateCover_image_le {Y : TopCat.{w}} {ι κ : Type*} (f : X ⟶ Y)
    (U : ι → Set X) (V : κ → Set Y)
    (h : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V := by
  have h_eq : (subordinateCover U).image (TopCat.toSSet.map f) =
      ⨆ i, (subordinateSet (U i)).image (TopCat.toSSet.map f) := by
    dsimp [subordinateCover]
    rw [SSet.Subcomplex.image_iSup]
  rw [h_eq]
  apply iSup_le
  intro i
  obtain ⟨j, hj⟩ := h i
  calc (subordinateSet (U i)).image (TopCat.toSSet.map f)
      ≤ subordinateSet (X := Y) (V j) := subordinateSet_image_le f hj
    _ ≤ subordinateCover (X := Y) V := le_iSup (fun k => subordinateSet (V k)) j

lemma subordinateCover_preimage {Y : TopCat.{w}} {κ : Type*} (f : X ⟶ Y)
    (V : κ → Set Y) :
    (subordinateCover (X := Y) V).preimage (TopCat.toSSet.map f) =
      subordinateCover (fun k => f ⁻¹' (V k)) := by
  dsimp [subordinateCover]
  rw [SSet.Subcomplex.preimage_iSup]
  congr 1
  ext k
  rw [subordinateSet_preimage]

noncomputable abbrev singularSSetMap {Y : TopCat.{w}} (f : X ⟶ Y) :
    TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj Y :=
  TopCat.toSSet.map f

noncomputable def subordinateCoverSSetMap {Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    (subordinateCover U).toSSet ⟶ (subordinateCover (X := Y) V).toSSet :=
  SSet.Subcomplex.lift ((subordinateCover U).ι ≫ TopCat.toSSet.map f)
    (by
      have : SSet.Subcomplex.range ((subordinateCover U).ι ≫ TopCat.toSSet.map f) =
          (subordinateCover U).image (TopCat.toSSet.map f) := by
        rw [SSet.Subcomplex.image_eq_range]
      rw [this]
      exact h)

lemma subordinateCoverSSetMap_ι {Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    subordinateCoverSSetMap f U V h ≫ (subordinateCover (X := Y) V).ι =
      (subordinateCover U).ι ≫ TopCat.toSSet.map f := by
  simp [subordinateCoverSSetMap]

lemma subordinateCoverSSetMap_proof_irrel {Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h₁ h₂ : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    subordinateCoverSSetMap f U V h₁ = subordinateCoverSSetMap f U V h₂ := by
  have eq1 : subordinateCoverSSetMap f U V h₁ ≫ (subordinateCover (X := Y) V).ι =
      (subordinateCover U).ι ≫ TopCat.toSSet.map f := subordinateCoverSSetMap_ι f U V h₁
  have eq2 : subordinateCoverSSetMap f U V h₂ ≫ (subordinateCover (X := Y) V).ι =
      (subordinateCover U).ι ≫ TopCat.toSSet.map f := subordinateCoverSSetMap_ι f U V h₂
  have heq : subordinateCoverSSetMap f U V h₁ ≫ (subordinateCover (X := Y) V).ι =
      subordinateCoverSSetMap f U V h₂ ≫ (subordinateCover (X := Y) V).ι :=
    Eq.trans eq1 eq2.symm
  exact (cancel_mono (f := (subordinateCover (X := Y) V).ι)).mp heq

noncomputable def subordinateCoverSSetMapOfMapsTo {Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (hMaps : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    (subordinateCover U).toSSet ⟶ (subordinateCover (X := Y) V).toSSet :=
  subordinateCoverSSetMap f U V (subordinateCover_image_le f U V hMaps)

noncomputable def smallCoverInter (A B : Set X) : Unit → Set X := fun _ => A ∩ B
noncomputable def smallCoverLeft (A : Set X) : Unit → Set X := fun _ => A
noncomputable def smallCoverRight (B : Set X) : Unit → Set X := fun _ => B
noncomputable def smallCoverBoth (A B : Set X) : Bool → Set X := fun b => if b then A else B

end SmallChainsTop

section SmallChainsChain

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Small chains are ordinary simplicial chains of the subordinate subcomplex. -/
noncomputable abbrev smallChainComplex {ι : Type*} (R : C) (U : ι → Set X) :
    ChainComplex C ℕ :=
  ((SSet.chainComplexFunctor C).obj R).obj (subordinateCover U).toSSet

/-- The small-chain inclusion comes from the subcomplex inclusion. -/
noncomputable abbrev smallChainInclusion {ι : Type*} (R : C) (U : ι → Set X) :
    smallChainComplex R U ⟶ ((SSet.chainComplexFunctor C).obj R).obj (TopCat.toSSet.obj X) :=
  ((SSet.chainComplexFunctor C).obj R).map (subordinateCover U).ι

/-- Refinement maps require only an inequality of subordinate subcomplexes. -/
noncomputable abbrev smallChainMapOfLE {ι κ : Type*} (R : C) (U : ι → Set X) (V : κ → Set X)
    (h : subordinateCover U ≤ subordinateCover V) :
    smallChainComplex R U ⟶ smallChainComplex R V :=
  ((SSet.chainComplexFunctor C).obj R).map (SSet.Subcomplex.homOfLE h)

noncomputable abbrev singularChainMap {Y : TopCat.{w}} (R : C) (f : X ⟶ Y) :
    ((SSet.chainComplexFunctor C).obj R).obj (TopCat.toSSet.obj X) ⟶
      ((SSet.chainComplexFunctor C).obj R).obj (TopCat.toSSet.obj Y) :=
  ((SSet.chainComplexFunctor C).obj R).map (TopCat.toSSet.map f)

noncomputable def smallChainMapOfImageLE {Y : TopCat.{w}} {ι κ : Type*}
    (R : C) (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    smallChainComplex R U ⟶ smallChainComplex (X := Y) R V :=
  ((SSet.chainComplexFunctor C).obj R).map (subordinateCoverSSetMap f U V h)

noncomputable def smallChainMapOfMapsTo {Y : TopCat.{w}} {ι κ : Type*}
    (R : C) (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (hMaps : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    smallChainComplex R U ⟶ smallChainComplex (X := Y) R V :=
  smallChainMapOfImageLE R f U V (subordinateCover_image_le f U V hMaps)

end SmallChainsChain

section SmallChainsSimplicialLaws

private lemma subordinateCoverSSetMap_id_aux {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    (h : (subordinateCover U).image (TopCat.toSSet.map (𝟙 X)) ≤ subordinateCover U) :
    subordinateCoverSSetMap (𝟙 X) U U h = 𝟙 _ := by
  rw [← cancel_mono (f := (subordinateCover U).ι)]
  calc subordinateCoverSSetMap (𝟙 X) U U h ≫ (subordinateCover U).ι
      = (subordinateCover U).ι ≫ TopCat.toSSet.map (𝟙 X) := subordinateCoverSSetMap_ι _ _ _ _
    _ = (subordinateCover U).ι ≫ 𝟙 _ := by rw [TopCat.toSSet.map_id]
    _ = (subordinateCover U).ι := by rw [Category.comp_id]
    _ = 𝟙 _ ≫ (subordinateCover U).ι := by rw [Category.id_comp]

@[simp]
lemma subordinateCoverSSetMap_id {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) :
    subordinateCoverSSetMap (𝟙 X) U U
        (by
          calc (subordinateCover U).image (TopCat.toSSet.map (𝟙 X))
              = subordinateCover U := by
                rw [TopCat.toSSet.map_id, SSet.Subcomplex.image_id]
            _ ≤ subordinateCover U := le_rfl) = 𝟙 _ :=
  subordinateCoverSSetMap_id_aux U _

lemma subordinateCoverSSetMap_refinement {X : TopCat.{w}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set X)
    (h_le : subordinateCover U ≤ subordinateCover V)
    (h_im : (subordinateCover U).image (TopCat.toSSet.map (𝟙 X)) ≤ subordinateCover V) :
    subordinateCoverSSetMap (𝟙 X) U V h_im = SSet.Subcomplex.homOfLE h_le := by
  rw [← cancel_mono (f := (subordinateCover V).ι)]
  calc subordinateCoverSSetMap (𝟙 X) U V h_im ≫ (subordinateCover V).ι
      = (subordinateCover U).ι ≫ TopCat.toSSet.map (𝟙 X) := subordinateCoverSSetMap_ι _ _ _ _
    _ = (subordinateCover U).ι ≫ 𝟙 _ := by rw [TopCat.toSSet.map_id]
    _ = (subordinateCover U).ι := by rw [Category.comp_id]
    _ = SSet.Subcomplex.homOfLE h_le ≫ (subordinateCover V).ι := by
        rw [SSet.Subcomplex.homOfLE_ι]

lemma subordinateCoverImageLE_comp {X Y Z : TopCat.{w}} {ι κ μ : Type*}
    {f : X ⟶ Y} {g : Y ⟶ Z} {U : ι → Set X} {V : κ → Set Y} {W : μ → Set Z}
    (h₁ : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover V)
    (h₂ : (subordinateCover V).image (TopCat.toSSet.map g) ≤ subordinateCover W) :
    (subordinateCover U).image (TopCat.toSSet.map (f ≫ g)) ≤ subordinateCover W := by
  have h_eq : (subordinateCover U).image (TopCat.toSSet.map (f ≫ g)) =
      ((subordinateCover U).image (TopCat.toSSet.map f)).image (TopCat.toSSet.map g) := by
    rw [TopCat.toSSet.map_comp, SSet.Subcomplex.image_comp]
  rw [h_eq]
  calc ((subordinateCover U).image (TopCat.toSSet.map f)).image (TopCat.toSSet.map g)
      ≤ (subordinateCover V).image (TopCat.toSSet.map g) :=
        SSet.Subcomplex.image_monotone _ h₁
    _ ≤ subordinateCover W := h₂

lemma subordinateCoverSSetMap_comp {X Y Z : TopCat.{w}} {ι κ μ : Type*}
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : ι → Set X) (V : κ → Set Y) (W : μ → Set Z)
    (h₁ : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover V)
    (h₂ : (subordinateCover V).image (TopCat.toSSet.map g) ≤ subordinateCover W) :
    subordinateCoverSSetMap f U V h₁ ≫ subordinateCoverSSetMap g V W h₂ =
      subordinateCoverSSetMap (f ≫ g) U W (subordinateCoverImageLE_comp h₁ h₂) := by
  have h_eq : (subordinateCoverSSetMap f U V h₁ ≫ subordinateCoverSSetMap g V W h₂) ≫
      (subordinateCover W).ι =
      (subordinateCover U).ι ≫ TopCat.toSSet.map (f ≫ g) := by
    calc (subordinateCoverSSetMap f U V h₁ ≫ subordinateCoverSSetMap g V W h₂) ≫
          (subordinateCover W).ι
        = subordinateCoverSSetMap f U V h₁ ≫
            (subordinateCoverSSetMap g V W h₂ ≫ (subordinateCover W).ι) := by
          rw [Category.assoc]
      _ = subordinateCoverSSetMap f U V h₁ ≫
            ((subordinateCover V).ι ≫ TopCat.toSSet.map g) := by
          rw [subordinateCoverSSetMap_ι]
      _ = (subordinateCoverSSetMap f U V h₁ ≫ (subordinateCover V).ι) ≫
            TopCat.toSSet.map g := by
          rw [← Category.assoc]
      _ = ((subordinateCover U).ι ≫ TopCat.toSSet.map f) ≫ TopCat.toSSet.map g := by
          rw [subordinateCoverSSetMap_ι]
      _ = (subordinateCover U).ι ≫ (TopCat.toSSet.map f ≫ TopCat.toSSet.map g) := by
          rw [Category.assoc]
      _ = (subordinateCover U).ι ≫ TopCat.toSSet.map (f ≫ g) := by
          rw [← TopCat.toSSet.map_comp]
  have h2 : subordinateCoverSSetMap (f ≫ g) U W (subordinateCoverImageLE_comp h₁ h₂) ≫
      (subordinateCover W).ι = (subordinateCover U).ι ≫ TopCat.toSSet.map (f ≫ g) :=
    subordinateCoverSSetMap_ι _ _ _ _
  rw [← h2] at h_eq
  rw [cancel_mono (f := (subordinateCover W).ι)] at h_eq
  exact h_eq

end SmallChainsSimplicialLaws

section SmallChainsChainLaws

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

@[simp]
lemma smallChainMapOfLE_refl {ι : Type*} (R : C) (U : ι → Set X) :
    smallChainMapOfLE R U U le_rfl = 𝟙 _ := by
  dsimp [smallChainMapOfLE]
  simp

lemma smallChainMapOfLE_comp {ι κ μ : Type*} (R : C) (U : ι → Set X) (V : κ → Set X) (W : μ → Set X)
    {hUV : subordinateCover U ≤ subordinateCover V}
    {hVW : subordinateCover V ≤ subordinateCover W} :
    smallChainMapOfLE R U V hUV ≫ smallChainMapOfLE R V W hVW =
      smallChainMapOfLE R U W (hUV.trans hVW) := by
  dsimp [smallChainMapOfLE]
  rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_comp]

@[simp]
lemma smallChainMapOfLE_comp_inclusion {ι κ : Type*} (R : C) (U : ι → Set X) (V : κ → Set X)
    (h : subordinateCover U ≤ subordinateCover V) :
    smallChainMapOfLE R U V h ≫ smallChainInclusion R V = smallChainInclusion R U := by
  change ((SSet.chainComplexFunctor C).obj R).map (SSet.Subcomplex.homOfLE h) ≫
      ((SSet.chainComplexFunctor C).obj R).map (subordinateCover V).ι =
    ((SSet.chainComplexFunctor C).obj R).map (subordinateCover U).ι
  rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]

lemma smallChainMapOfImageLE_proof_irrel {Y : TopCat.{w}} {ι κ : Type*}
    (R : C) (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h₁ h₂ : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    smallChainMapOfImageLE R f U V h₁ = smallChainMapOfImageLE R f U V h₂ :=
  rfl

@[simp]
lemma smallChainMapOfImageLE_comp_inclusion {Y : TopCat.{w}} {ι κ : Type*}
    (R : C) (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    smallChainMapOfImageLE R f U V h ≫ smallChainInclusion (X := Y) R V =
      smallChainInclusion R U ≫ singularChainMap R f := by
  dsimp [smallChainMapOfImageLE, smallChainInclusion, singularChainMap]
  calc ((SSet.chainComplexFunctor C).obj R).map (subordinateCoverSSetMap f U V h) ≫
        ((SSet.chainComplexFunctor C).obj R).map (subordinateCover V).ι
      = ((SSet.chainComplexFunctor C).obj R).map
          (subordinateCoverSSetMap f U V h ≫ (subordinateCover V).ι) := by
        rw [← Functor.map_comp]
    _ = ((SSet.chainComplexFunctor C).obj R).map
          ((subordinateCover U).ι ≫ TopCat.toSSet.map f) := by
        rw [subordinateCoverSSetMap_ι]
    _ = ((SSet.chainComplexFunctor C).obj R).map (subordinateCover U).ι ≫
        ((SSet.chainComplexFunctor C).obj R).map (TopCat.toSSet.map f) := by
        rw [Functor.map_comp]

@[simp]
lemma smallChainMapOfMapsTo_comp_inclusion {Y : TopCat.{w}} {ι κ : Type*}
    (R : C) (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (hMaps : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    smallChainMapOfMapsTo R f U V hMaps ≫ smallChainInclusion (X := Y) R V =
      smallChainInclusion R U ≫ singularChainMap R f := by
  dsimp [smallChainMapOfMapsTo]
  exact smallChainMapOfImageLE_comp_inclusion R f U V _

end SmallChainsChainLaws

section SmallChainsChainLawsRest

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

lemma smallChainMapOfImageLE_id_aux {X : TopCat.{w}} {ι : Type*} (R : C) (U : ι → Set X)
    (h : (subordinateCover U).image (TopCat.toSSet.map (𝟙 X)) ≤ subordinateCover U) :
    smallChainMapOfImageLE (X := X) R (𝟙 X) U U h = 𝟙 _ := by
  dsimp [smallChainMapOfImageLE]
  rw [subordinateCoverSSetMap_id_aux U h]
  simp

@[simp]
lemma smallChainMapOfImageLE_id {X : TopCat.{w}} {ι : Type*} (R : C) (U : ι → Set X) :
    smallChainMapOfImageLE (X := X) R (𝟙 X) U U
        (by
          calc (subordinateCover U).image (TopCat.toSSet.map (𝟙 X))
              = subordinateCover U := by
                rw [TopCat.toSSet.map_id, SSet.Subcomplex.image_id]
            _ ≤ subordinateCover U := le_rfl) = 𝟙 _ :=
  smallChainMapOfImageLE_id_aux R U _

lemma smallChainMap_refinement {X : TopCat.{w}} {ι κ : Type*} (R : C)
    (U : ι → Set X) (V : κ → Set X)
    (h_le : subordinateCover U ≤ subordinateCover V)
    (h_im : (subordinateCover U).image (TopCat.toSSet.map (𝟙 X)) ≤ subordinateCover V) :
    smallChainMapOfImageLE (X := X) R (𝟙 X) U V h_im = smallChainMapOfLE R U V h_le := by
  dsimp [smallChainMapOfImageLE, smallChainMapOfLE]
  rw [subordinateCoverSSetMap_refinement U V h_le h_im]

@[simp]
lemma smallChainMapOfImageLE_comp {X Y Z : TopCat.{w}} {ι κ μ : Type*}
    (R : C) (f : X ⟶ Y) (g : Y ⟶ Z) (U : ι → Set X) (V : κ → Set Y) (W : μ → Set Z)
    (h₁ : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover V)
    (h₂ : (subordinateCover V).image (TopCat.toSSet.map g) ≤ subordinateCover W) :
    smallChainMapOfImageLE R f U V h₁ ≫ smallChainMapOfImageLE (X := Y) R g V W h₂ =
      smallChainMapOfImageLE R (f ≫ g) U W (subordinateCoverImageLE_comp h₁ h₂) := by
  dsimp [smallChainMapOfImageLE]
  rw [← Functor.map_comp, subordinateCoverSSetMap_comp]

end SmallChainsChainLawsRest

section SmallChainsCoefficient
variable (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
noncomputable def smallChainCoefficientFunctor {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) :
    C ⥤ ChainComplex C ℕ :=
  (SSet.chainComplexFunctor C).flip.obj (subordinateCover U).toSSet
@[simp] lemma smallChainCoefficientFunctor_obj {X : TopCat.{w}} {ι : Type*}
    (U : ι → Set X) (R : C) :
    (smallChainCoefficientFunctor C U).obj R = smallChainComplex R U := rfl
@[simp] lemma smallChainCoefficientFunctor_map {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    {R S : C} (f : R ⟶ S) :
    (smallChainCoefficientFunctor C U).map f =
      ((SSet.chainComplexFunctor C).map f).app (subordinateCover U).toSSet := rfl
instance smallChainCoefficientFunctor_additive {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) :
    (smallChainCoefficientFunctor C U).Additive where
  map_add {R S} f g := by
    simp only [smallChainCoefficientFunctor]
    have h_add := (SSet.chainComplexFunctor C).map_add (f := f) (g := g)
    have h_app :
        ((SSet.chainComplexFunctor C).map (f + g)).app (subordinateCover U).toSSet =
          ((SSet.chainComplexFunctor C).map f +
            (SSet.chainComplexFunctor C).map g).app
            (subordinateCover U).toSSet := by rw [h_add]
    simp only [NatTrans.app_add] at h_app; exact h_app
noncomputable def smallChainInclusionNatTrans {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) :
    smallChainCoefficientFunctor C U ⟶ (singularChainComplexFunctor C).flip.obj X :=
  (SSet.chainComplexFunctor C).flip.map (subordinateCover U).ι
@[simp] lemma smallChainInclusionNatTrans_app {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    (R : C) :
    (smallChainInclusionNatTrans C U).app R = smallChainInclusion R U := rfl
noncomputable def smallChainMapOfLENatTrans {X : TopCat.{w}} {ι κ : Type*} (U : ι → Set X)
    (V : κ → Set X) (h : subordinateCover U ≤ subordinateCover V) :
    smallChainCoefficientFunctor C U ⟶ smallChainCoefficientFunctor C V :=
  (SSet.chainComplexFunctor C).flip.map (SSet.Subcomplex.homOfLE h)
@[simp] lemma smallChainMapOfLENatTrans_app {X : TopCat.{w}} {ι κ : Type*} (U : ι → Set X)
    (V : κ → Set X) (h : subordinateCover U ≤ subordinateCover V) (R : C) :
    (smallChainMapOfLENatTrans C U V h).app R = smallChainMapOfLE R U V h := rfl
noncomputable def smallChainMapOfImageLENatTrans {X Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    smallChainCoefficientFunctor (C := C) (X := X) U ⟶
      smallChainCoefficientFunctor (C := C) (X := Y) V :=
  (SSet.chainComplexFunctor C).flip.map (subordinateCoverSSetMap f U V h)
@[simp] lemma smallChainMapOfImageLENatTrans_app {X Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V)
    (R : C) :
    (smallChainMapOfImageLENatTrans (C := C) f U V h).app R =
      smallChainMapOfImageLE R f U V h := rfl
noncomputable def smallChainMapOfMapsToNatTrans {X Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (hMaps : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    smallChainCoefficientFunctor (C := C) (X := X) U ⟶
      smallChainCoefficientFunctor (C := C) (X := Y) V :=
  (SSet.chainComplexFunctor C).flip.map
    (subordinateCoverSSetMap f U V (subordinateCover_image_le f U V hMaps))
@[simp] lemma smallChainMapOfMapsToNatTrans_app {X Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (hMaps : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) (R : C) :
    (smallChainMapOfMapsToNatTrans (C := C) f U V hMaps).app R =
      smallChainMapOfMapsTo R f U V hMaps := rfl
@[simp] lemma smallChainMapOfLENatTrans_refl {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) :
    smallChainMapOfLENatTrans C U U le_rfl = 𝟙 _ := by ext R; simp
lemma smallChainMapOfLENatTrans_comp {X : TopCat.{w}} {ι κ μ : Type*}
    (U : ι → Set X) (V : κ → Set X) (W : μ → Set X)
    {hUV : subordinateCover U ≤ subordinateCover V}
    {hVW : subordinateCover V ≤ subordinateCover W} :
    smallChainMapOfLENatTrans C U V hUV ≫ smallChainMapOfLENatTrans C V W hVW =
      smallChainMapOfLENatTrans C U W (hUV.trans hVW) := by ext R; simp [smallChainMapOfLE_comp]
@[simp] lemma smallChainMapOfLENatTrans_comp_inclusion {X : TopCat.{w}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set X)
    (h : subordinateCover U ≤ subordinateCover V) :
    smallChainMapOfLENatTrans C U V h ≫ smallChainInclusionNatTrans C V =
      smallChainInclusionNatTrans C U := by
  apply NatTrans.ext; funext R
  simp only [NatTrans.comp_app, smallChainMapOfLENatTrans_app, smallChainInclusionNatTrans_app]
  exact smallChainMapOfLE_comp_inclusion R U V h
@[simp] lemma smallChainMapOfImageLENatTrans_id {X : TopCat.{w}} {ι : Type*}
    (U : ι → Set X) :
    smallChainMapOfImageLENatTrans (C := C) (𝟙 X) U U
        (by rw [TopCat.toSSet.map_id, SSet.Subcomplex.image_id]) = 𝟙 _ := by
  ext R; simp
lemma smallChainMapOfImageLENatTrans_comp {X Y Z : TopCat.{w}} {ι κ μ : Type*}
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : ι → Set X) (V : κ → Set Y) (W : μ → Set Z)
    (h₁ : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover V)
    (h₂ : (subordinateCover V).image (TopCat.toSSet.map g) ≤ subordinateCover W) :
    smallChainMapOfImageLENatTrans (C := C) f U V h₁ ≫
        smallChainMapOfImageLENatTrans (C := C) g V W h₂ =
      smallChainMapOfImageLENatTrans (C := C) (f ≫ g) U W
        (subordinateCoverImageLE_comp h₁ h₂) := by
  ext R; simp [smallChainMapOfImageLE_comp]
@[simp] lemma smallChainMapOfImageLENatTrans_comp_inclusion {X Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤ subordinateCover (X := Y) V) :
    smallChainMapOfImageLENatTrans (C := C) f U V h ≫
        smallChainInclusionNatTrans (C := C) (X := Y) V =
      smallChainInclusionNatTrans (C := C) (X := X) U ≫
        (singularChainComplexFunctor C).flip.map f := by
  apply NatTrans.ext; funext R
  simp only [NatTrans.comp_app, smallChainMapOfImageLENatTrans_app,
    smallChainInclusionNatTrans_app, Functor.flip_map_app]
  have h_comp := smallChainMapOfImageLE_comp_inclusion (C := C) R f U V h
  have h_sing : singularChainMap (C := C) R f =
      ((singularChainComplexFunctor C).obj R).map f := rfl
  rw [h_sing] at h_comp; exact h_comp
@[simp] lemma smallChainMapOfMapsToNatTrans_comp_inclusion {X Y : TopCat.{w}} {ι κ : Type*}
    (f : X ⟶ Y) (U : ι → Set X) (V : κ → Set Y)
    (hMaps : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    smallChainMapOfMapsToNatTrans (C := C) f U V hMaps ≫
        smallChainInclusionNatTrans (C := C) (X := Y) V =
      smallChainInclusionNatTrans (C := C) (X := X) U ≫
        (singularChainComplexFunctor C).flip.map f := by
  apply NatTrans.ext; funext R
  simp only [NatTrans.comp_app, smallChainMapOfMapsToNatTrans_app,
    smallChainInclusionNatTrans_app, Functor.flip_map_app]
  have h_comp := smallChainMapOfMapsTo_comp_inclusion (C := C) R f U V hMaps
  have h_sing : singularChainMap (C := C) R f =
      ((singularChainComplexFunctor C).obj R).map f := rfl
  rw [h_sing] at h_comp; exact h_comp

end SmallChainsCoefficient

section SmallChainsMono

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {X : TopCat.{w}} {ι : Type*} {U : ι → Set X} {R : C}

instance smallChainInclusion_mono (R : C) (U : ι → Set X) :
    Mono (smallChainInclusion (X := X) (C := C) R U) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let p : (subordinateCover (X := X) U).toSSet.obj (Opposite.op (⦋n⦌)) →
      (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌)) :=
    (subordinateCover (X := X) U).ι.app (Opposite.op (⦋n⦌))
  have h_inj : Function.Injective p := by
    intro a b h
    dsimp [p] at h
    cases a with
    | mk val prop =>
      cases b with
      | mk val2 prop2 =>
        have h_val : val = val2 := h
        exact Subtype.ext h_val
  have h_eq : (smallChainInclusion (X := X) (C := C) R U).f n =
      Sigma.map'
        (f := fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌)) => R)
        (g := fun _ : (subordinateCover (X := X) U).toSSet.obj (Opposite.op (⦋n⦌)) => R)
        p (fun _ => 𝟙 R) := by
    apply SSet.chainComplex_hom_ext
    intro x
    have h1 : ((subordinateCover U).toSSet).ιChainComplex (R := R) x ≫
        (smallChainInclusion (X := X) (C := C) R U).f n =
        (TopCat.toSSet.obj X).ιChainComplex (R := R) (p x) := by
      have h := SSet.ι_chainComplexMap_f
        (X := (subordinateCover (X := X) U).toSSet)
        (Y := TopCat.toSSet.obj X)
        ((subordinateCover (X := X) U).ι) R x
      exact h
    have h2 : ((subordinateCover U).toSSet).ιChainComplex (R := R) x ≫
        Sigma.map'
          (f := fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌)) => R)
          (g := fun _ : (subordinateCover U).toSSet.obj (Opposite.op (⦋n⦌)) => R)
          p (fun _ => 𝟙 R) =
        (TopCat.toSSet.obj X).ιChainComplex (R := R) (p x) := by
      have h2' : Sigma.ι (fun _ : (subordinateCover U).toSSet.obj (Opposite.op (⦋n⦌)) => R) x ≫
          Sigma.map'
            (f := fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌)) => R)
            (g := fun _ : (subordinateCover U).toSSet.obj (Opposite.op (⦋n⦌)) => R)
            p (fun _ => 𝟙 R) =
          Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌)) => R) (p x) := by
        simp
      dsimp [SSet.ιChainComplex]
      exact h2'
    exact h1.trans h2.symm
  have h_mono : Mono
      (Sigma.map'
        (f := fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌)) => R)
        (g := fun _ : (subordinateCover (X := X) U).toSSet.obj (Opposite.op (⦋n⦌)) => R)
        p (fun _ => 𝟙 R)) := by
    have : MonoCoprod C := inferInstance
    exact MonoCoprod.mono_map'_of_injective
      (X := fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌)) => R) p h_inj
  rw [h_eq]
  exact h_mono

end SmallChainsMono

section SmallChainSplitting

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

noncomputable def smallChainProjection (R : C)
    {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) (n : ℕ) :
    (((SSet.chainComplexFunctor C).obj R).obj
      (TopCat.toSSet.obj X)).X n ⟶
      (smallChainComplex (C := C) R U).X n :=
  Sigma.desc fun σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) =>
    @dite _ (σ ∈ (subordinateCover U).obj
        (Opposite.op (SimplexCategory.mk n))) (Classical.dec _)
      (fun h => (subordinateCover U).toSSet.ιChainComplex
        (R := R) ⟨σ, h⟩) (fun _ => 0)

@[reassoc (attr := simp)]
lemma smallChainInclusion_comp_projection (R : C)
    {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) (n : ℕ) :
    (smallChainInclusion (C := C) R U).f n ≫
        smallChainProjection R U n =
      𝟙 ((smallChainComplex (C := C) R U).X n) := by
  refine SSet.chainComplex_hom_ext
      (X := (subordinateCover U).toSSet) (R := R) (n := n) ?_
  intro x
  have h1 : (subordinateCover U).toSSet.ιChainComplex (R := R) x ≫
      (smallChainInclusion (C := C) R U).f n ≫
        smallChainProjection R U n =
      (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((subordinateCover U).ι.app _ x) ≫
        smallChainProjection R U n := by
    rw [SSet.ι_chainComplexMap_f_assoc]
  rw [h1]
  have h2 : (subordinateCover U).ι.app
      (Opposite.op (SimplexCategory.mk n)) x = x.1 := rfl
  rw [h2]
  have : (TopCat.toSSet.obj X).ιChainComplex (R := R) x.1 ≫
      smallChainProjection R U n =
      (subordinateCover U).toSSet.ιChainComplex (R := R) x := by
    have hmem : x.1 ∈ (subordinateCover U).obj
        (Opposite.op (SimplexCategory.mk n)) := x.2
    calc (TopCat.toSSet.obj X).ιChainComplex (R := R) x.1 ≫
        smallChainProjection R U n
        = Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk n)) => R) x.1 ≫
          smallChainProjection R U n := rfl
      _ = (fun σ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk n)) =>
          @dite _ (σ ∈ (subordinateCover U).obj
              (Opposite.op (SimplexCategory.mk n)))
            (Classical.dec _) (fun h =>
              (subordinateCover U).toSSet.ιChainComplex
                (R := R) ⟨σ, h⟩) (fun _ => 0)) x.1 := by
        simp only [smallChainProjection, Sigma.ι_comp_desc]
      _ = @dite _ (x.1 ∈ (subordinateCover U).obj
            (Opposite.op (SimplexCategory.mk n)))
          (Classical.dec _) (fun h =>
            (subordinateCover U).toSSet.ιChainComplex
              (R := R) ⟨x.1, h⟩) (fun _ => 0) := rfl
      _ = (subordinateCover U).toSSet.ιChainComplex
          (R := R) ⟨x.1, hmem⟩ := by
        simp [hmem]
      _ = (subordinateCover U).toSSet.ιChainComplex
          (R := R) x := by
        have heq : (⟨x.1, hmem⟩ :
            (subordinateCover U).toSSet.obj
              (Opposite.op (SimplexCategory.mk n))) = x := by
          ext
          rfl
        rw [heq]
  rw [this]
  rw [Category.comp_id]

noncomputable instance smallChainInclusion_f_isSplitMono
    (R : C) {X : TopCat.{w}} {ι : Type*}
    (U : ι → Set X) (n : ℕ) :
    IsSplitMono ((smallChainInclusion (C := C) R U).f n) :=
  IsSplitMono.mk' ⟨smallChainProjection R U n,
    smallChainInclusion_comp_projection R U n⟩

end SmallChainSplitting

end AlgebraicTopology
