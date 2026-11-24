/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadTensorHom

/-!
# Associator Quad Index

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory
namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadIndex
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
attribute [local instance] Enriched.prodCategory
/-- The full four-input product `((I × I) × I) × I` for the index pentagon. -/
abbrev indices := ((I × I) × I) × I
/-- Partially tensor the first two indices to form the triple `((i ⊗ j, k), l)`. -/
abbrev abInput : EnrichedFunctor V (indices (I := I)) ((I × I) × I) :=
  prodEnrichedFunctor (prodEnrichedFunctor d.tensorEnrichedFunctor (EnrichedFunctor.id V I))
    (EnrichedFunctor.id V I)
/-- Reassociate the four-input product into `(i, j)` and `(k, l)` using the enriched
  product associator. -/
abbrev pairs : EnrichedFunctor V (indices (I := I)) ((I × I) × (I × I)) :=
  Associator.productAssociator (V := V) (A := I × I) (B := I) (C := I)
/-- Form the triple `((i, j), k ⊗ l)` by partially tensoring the final two indices. -/
abbrev bcInput : EnrichedFunctor V (indices (I := I)) ((I × I) × I) :=
  (pairs (V := V) (I := I)).comp V
    (prodEnrichedFunctor (EnrichedFunctor.id V (I × I)) d.tensorEnrichedFunctor)
/-- The enriched partial tensor `((i, j), k) ↦ (i, j ⊗ k)`. -/
abbrev middle : EnrichedFunctor V ((I × I) × I) (I × I) :=
  (Associator.productAssociator (V := V) (A := I) (B := I) (C := I)).comp V
    (prodEnrichedFunctor (EnrichedFunctor.id V I) d.tensorEnrichedFunctor)
/-- Form the triple `((i, j ⊗ k), l)` by partially tensoring the middle two indices. -/
abbrev deInput : EnrichedFunctor V (indices (I := I)) ((I × I) × I) :=
  prodEnrichedFunctor (middle d) (EnrichedFunctor.id V I)
/-- Reassociate the four-input product as `(i, ((j, k), l))` with its full enriched Hom
  action. -/
abbrev front : EnrichedFunctor V (indices (I := I)) (I × ((I × I) × I)) :=
  (prodEnrichedFunctor (Associator.productAssociator (V := V) (A := I) (B := I) (C := I))
    (EnrichedFunctor.id V I)).comp V
      (Associator.productAssociator (V := V) (A := I) (B := I × I) (C := I))

/-- The five original index tensor words on the unchanged full four-input product. -/
abbrev indexA : EnrichedFunctor V (indices (I := I)) I :=
  (prodEnrichedFunctor (AssociatorIndex.leftIndex d) (EnrichedFunctor.id V I)).comp V
    d.tensorEnrichedFunctor
/-- The enriched index tensor with parenthesization `(i ⊗ j) ⊗ (k ⊗ l)`. -/
abbrev indexB : EnrichedFunctor V (indices (I := I)) I :=
  (abInput d).comp V (AssociatorIndex.rightIndex d)
/-- The fully right-associated enriched index tensor `i ⊗ (j ⊗ (k ⊗ l))`. -/
abbrev indexC : EnrichedFunctor V (indices (I := I)) I :=
  (bcInput d).comp V (AssociatorIndex.rightIndex d)
/-- The enriched index tensor with parenthesization `(i ⊗ (j ⊗ k)) ⊗ l`. -/
abbrev indexD : EnrichedFunctor V (indices (I := I)) I :=
  (prodEnrichedFunctor (AssociatorIndex.rightIndex d) (EnrichedFunctor.id V I)).comp V
    d.tensorEnrichedFunctor
/-- The enriched index tensor with parenthesization `i ⊗ ((j ⊗ k) ⊗ l)`. -/
abbrev indexE : EnrichedFunctor V (indices (I := I)) I :=
  (deInput d).comp V (AssociatorIndex.rightIndex d)

/-- The index associator from `((i ⊗ j) ⊗ k) ⊗ l` to `(i ⊗ j) ⊗ (k ⊗ l)`. -/
abbrev edgeAB (X : indices (I := I)) : (indexA d).obj X ≅ (indexB d).obj X :=
  α_ (X.1.1.1 ⊗ X.1.1.2) X.1.2 X.2
/-- The index associator from `(i ⊗ j) ⊗ (k ⊗ l)` to `i ⊗ (j ⊗ (k ⊗ l))`. -/
abbrev edgeBC (X : indices (I := I)) : (indexB d).obj X ≅ (indexC d).obj X :=
  α_ X.1.1.1 X.1.1.2 (X.1.2 ⊗ X.2)
/-- The first-three index associator tensored with the identity of the fourth index. -/
abbrev edgeAD (X : indices (I := I)) : (indexA d).obj X ≅ (indexD d).obj X :=
  (α_ X.1.1.1 X.1.1.2 X.1.2) ⊗ᵢ Iso.refl X.2
/-- The index associator from `(i ⊗ (j ⊗ k)) ⊗ l` to `i ⊗ ((j ⊗ k) ⊗ l)`. -/
abbrev edgeDE (X : indices (I := I)) : (indexD d).obj X ≅ (indexE d).obj X :=
  α_ X.1.1.1 (X.1.1.2 ⊗ X.1.2) X.2
/-- The final-three index associator tensored on the left with the identity of the first
  index. -/
abbrev edgeEC (X : indices (I := I)) : (indexE d).obj X ≅ (indexC d).obj X :=
  Iso.refl X.1.1.1 ⊗ᵢ (α_ X.1.1.2 X.1.2 X.2)

/-- The source of AB is exactly the original fully left index on every full Hom. -/
theorem ab_left_map (X Y : indices (I := I)) :
    ((abInput d).comp V (AssociatorIndex.leftIndex d)).map X Y = (indexA d).map X Y := by
  let R₁ : V := X.1.1.1 ⟶[V] Y.1.1.1
  let R₂ : V := X.1.1.2 ⟶[V] Y.1.1.2
  let R₃ : V := X.1.2 ⟶[V] Y.1.2
  let R₄ : V := X.2 ⟶[V] Y.2
  let R₁₂ : V := (X.1.1.1 ⊗ X.1.1.2) ⟶[V] (Y.1.1.1 ⊗ Y.1.1.2)
  let R₁₂₃ : V := ((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2) ⟶[V] ((Y.1.1.1 ⊗ Y.1.1.2) ⊗ Y.1.2)
  let t : R₁ ⊗ R₂ ⟶ R₁₂ := d.tensorMap X.1.1.1 Y.1.1.1 X.1.1.2 Y.1.1.2
  let u : R₁₂ ⊗ R₃ ⟶ R₁₂₃ := d.tensorMap (X.1.1.1 ⊗ X.1.1.2) (Y.1.1.1 ⊗ Y.1.1.2) X.1.2 Y.1.2
  let v : R₁₂₃ ⊗ R₄ ⟶ (((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2) ⊗ X.2) ⟶[V]
      (((Y.1.1.1 ⊗ Y.1.1.2) ⊗ Y.1.2) ⊗ Y.2) :=
    d.tensorMap ((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2) ((Y.1.1.1 ⊗ Y.1.1.2) ⊗ Y.1.2) X.2 Y.2
  change ((t ⊗ₘ 𝟙 R₃) ⊗ₘ 𝟙 R₄) ≫ ((u ⊗ₘ 𝟙 R₄) ≫ v) =
    (((t ⊗ₘ 𝟙 R₃) ≫ u) ⊗ₘ 𝟙 R₄) ≫ v
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id]

/-- The source of BC is the same original AB target, including every Hom associator. -/
theorem bc_left_map (X Y : indices (I := I)) :
    ((bcInput d).comp V (AssociatorIndex.leftIndex d)).map X Y = (indexB d).map X Y := by
  let R₁ : V := X.1.1.1 ⟶[V] Y.1.1.1
  let R₂ : V := X.1.1.2 ⟶[V] Y.1.1.2
  let R₃ : V := X.1.2 ⟶[V] Y.1.2
  let R₄ : V := X.2 ⟶[V] Y.2
  let R₁₂ : V := (X.1.1.1 ⊗ X.1.1.2) ⟶[V] (Y.1.1.1 ⊗ Y.1.1.2)
  let R₃₄ : V := (X.1.2 ⊗ X.2) ⟶[V] (Y.1.2 ⊗ Y.2)
  let t : R₁ ⊗ R₂ ⟶ R₁₂ := d.tensorMap X.1.1.1 Y.1.1.1 X.1.1.2 Y.1.1.2
  let u : R₃ ⊗ R₄ ⟶ R₃₄ := d.tensorMap X.1.2 Y.1.2 X.2 Y.2
  let v : R₁₂ ⊗ R₃₄ ⟶ ((X.1.1.1 ⊗ X.1.1.2) ⊗ (X.1.2 ⊗ X.2)) ⟶[V]
      ((Y.1.1.1 ⊗ Y.1.1.2) ⊗ (Y.1.2 ⊗ Y.2)) :=
    d.tensorMap (X.1.1.1 ⊗ X.1.1.2) (Y.1.1.1 ⊗ Y.1.1.2) (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)
  change ((α_ (R₁ ⊗ R₂) R₃ R₄).hom ≫ (𝟙 (R₁ ⊗ R₂) ⊗ₘ u)) ≫
      ((t ⊗ₘ 𝟙 R₃₄) ≫ v) =
    ((t ⊗ₘ 𝟙 R₃) ⊗ₘ 𝟙 R₄) ≫ (α_ R₁₂ R₃ R₄).hom ≫ R₁₂ ◁ u ≫ v
  simp only [Category.assoc]
  rw [associator_naturality_assoc]
  simp only [id_tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

/-- The source of DE keeps the actual right first-three tensor and the actual final input. -/
theorem de_left_map (X Y : indices (I := I)) :
    ((deInput d).comp V (AssociatorIndex.leftIndex d)).map X Y = (indexD d).map X Y := by
  let R₁ : V := X.1.1.1 ⟶[V] Y.1.1.1
  let R₂ : V := X.1.1.2 ⟶[V] Y.1.1.2
  let R₃ : V := X.1.2 ⟶[V] Y.1.2
  let R₄ : V := X.2 ⟶[V] Y.2
  let R₂₃ : V := (X.1.1.2 ⊗ X.1.2) ⟶[V] (Y.1.1.2 ⊗ Y.1.2)
  let R₁₂₃ : V := (X.1.1.1 ⊗ (X.1.1.2 ⊗ X.1.2)) ⟶[V] (Y.1.1.1 ⊗ (Y.1.1.2 ⊗ Y.1.2))
  let t : R₂ ⊗ R₃ ⟶ R₂₃ := d.tensorMap X.1.1.2 Y.1.1.2 X.1.2 Y.1.2
  let u : R₁ ⊗ R₂₃ ⟶ R₁₂₃ := d.tensorMap X.1.1.1 Y.1.1.1 (X.1.1.2 ⊗ X.1.2) (Y.1.1.2 ⊗ Y.1.2)
  let v : R₁₂₃ ⊗ R₄ ⟶ ((X.1.1.1 ⊗ (X.1.1.2 ⊗ X.1.2)) ⊗ X.2) ⟶[V]
      ((Y.1.1.1 ⊗ (Y.1.1.2 ⊗ Y.1.2)) ⊗ Y.2) :=
    d.tensorMap (X.1.1.1 ⊗ (X.1.1.2 ⊗ X.1.2)) (Y.1.1.1 ⊗ (Y.1.1.2 ⊗ Y.1.2)) X.2 Y.2
  change (((α_ R₁ R₂ R₃).hom ≫ (𝟙 R₁ ⊗ₘ t)) ⊗ₘ 𝟙 R₄) ≫ ((u ⊗ₘ 𝟙 R₄) ≫ v) =
    (((α_ R₁ R₂ R₃).hom ≫ R₁ ◁ t ≫ u) ⊗ₘ 𝟙 R₄) ≫ v
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id]
  simp only [id_tensorHom, Category.assoc]

/-- AB retains the complete original enriched index naturality square. -/
theorem edgeAB_map (X Y : indices (I := I)) :
    (indexB d).map X Y = (indexA d).map X Y ≫ (Iso.eHomCongr V (edgeAB d X) (edgeAB d Y)).hom := by
  let A : I := (indexA d).obj X
  let B : I := (indexA d).obj Y
  let C : I := (indexB d).obj X
  let D : I := (indexB d).obj Y
  let P : V := X ⟶[V] Y
  let S : V := ((abInput d).obj X) ⟶[V] ((abInput d).obj Y)
  let t : P ⟶ S := (abInput d).map X Y
  let l : S ⟶ (A ⟶[V] B) := (AssociatorIndex.leftIndex d).map ((abInput d).obj X) ((abInput d).obj
    Y)
  let r : S ⟶ (C ⟶[V] D) := (AssociatorIndex.rightIndex d).map ((abInput d).obj X) ((abInput d).obj
    Y)
  let q : (A ⟶[V] B) ⟶ (C ⟶[V] D) := (Iso.eHomCongr V (edgeAB d X) (edgeAB d Y)).hom
  let out : P ⟶ (A ⟶[V] B) := (indexA d).map X Y
  have h : r = l ≫ q := AssociatorIndex.indexMap_congr d ((abInput d).obj X) ((abInput d).obj Y)
  have hl : t ≫ l = out := ab_left_map d X Y
  change t ≫ r = out ≫ q
  rw [h]
  exact (Category.assoc t l q).symm.trans (congrArg (fun z => z ≫ q) hl)

/-- BC retains the complete original enriched index naturality square. -/
theorem edgeBC_map (X Y : indices (I := I)) :
    (indexC d).map X Y = (indexB d).map X Y ≫ (Iso.eHomCongr V (edgeBC d X) (edgeBC d Y)).hom := by
  let A : I := (indexB d).obj X
  let B : I := (indexB d).obj Y
  let C : I := (indexC d).obj X
  let D : I := (indexC d).obj Y
  let P : V := X ⟶[V] Y
  let S : V := ((bcInput d).obj X) ⟶[V] ((bcInput d).obj Y)
  let t : P ⟶ S := (bcInput d).map X Y
  let l : S ⟶ (A ⟶[V] B) := (AssociatorIndex.leftIndex d).map ((bcInput d).obj X) ((bcInput d).obj
    Y)
  let r : S ⟶ (C ⟶[V] D) := (AssociatorIndex.rightIndex d).map ((bcInput d).obj X) ((bcInput d).obj
    Y)
  let q : (A ⟶[V] B) ⟶ (C ⟶[V] D) := (Iso.eHomCongr V (edgeBC d X) (edgeBC d Y)).hom
  let out : P ⟶ (A ⟶[V] B) := (indexB d).map X Y
  have h : r = l ≫ q := AssociatorIndex.indexMap_congr d ((bcInput d).obj X) ((bcInput d).obj Y)
  have hl : t ≫ l = out := bc_left_map d X Y
  change t ≫ r = out ≫ q
  rw [h]
  exact (Category.assoc t l q).symm.trans (congrArg (fun z => z ≫ q) hl)

/-- DE retains the complete original enriched index naturality square. -/
theorem edgeDE_map (X Y : indices (I := I)) :
    (indexE d).map X Y = (indexD d).map X Y ≫ (Iso.eHomCongr V (edgeDE d X) (edgeDE d Y)).hom := by
  let A : I := (indexD d).obj X
  let B : I := (indexD d).obj Y
  let C : I := (indexE d).obj X
  let D : I := (indexE d).obj Y
  let P : V := X ⟶[V] Y
  let S : V := ((deInput d).obj X) ⟶[V] ((deInput d).obj Y)
  let t : P ⟶ S := (deInput d).map X Y
  let l : S ⟶ (A ⟶[V] B) := (AssociatorIndex.leftIndex d).map ((deInput d).obj X) ((deInput d).obj
    Y)
  let r : S ⟶ (C ⟶[V] D) := (AssociatorIndex.rightIndex d).map ((deInput d).obj X) ((deInput d).obj
    Y)
  let q : (A ⟶[V] B) ⟶ (C ⟶[V] D) := (Iso.eHomCongr V (edgeDE d X) (edgeDE d Y)).hom
  let out : P ⟶ (A ⟶[V] B) := (indexD d).map X Y
  have h : r = l ≫ q := AssociatorIndex.indexMap_congr d ((deInput d).obj X) ((deInput d).obj Y)
  have hl : t ≫ l = out := de_left_map d X Y
  change t ≫ r = out ≫ q
  rw [h]
  exact (Category.assoc t l q).symm.trans (congrArg (fun z => z ≫ q) hl)

/-- AD tensors the entire original first-three associator with the actual fourth identity. -/
theorem edgeAD_map (X Y : indices (I := I)) :
    (indexD d).map X Y = (indexA d).map X Y ≫ (Iso.eHomCongr V (edgeAD d X) (edgeAD d Y)).hom := by
  let A : I := (X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2
  let B : I := (Y.1.1.1 ⊗ Y.1.1.2) ⊗ Y.1.2
  let C : I := X.1.1.1 ⊗ (X.1.1.2 ⊗ X.1.2)
  let D : I := Y.1.1.1 ⊗ (Y.1.1.2 ⊗ Y.1.2)
  let S : V := X.1 ⟶[V] Y.1
  let R : V := X.2 ⟶[V] Y.2
  let l : S ⟶ (A ⟶[V] B) := (AssociatorIndex.leftIndex d).map X.1 Y.1
  let r : S ⟶ (C ⟶[V] D) := (AssociatorIndex.rightIndex d).map X.1 Y.1
  let q : (A ⟶[V] B) ⟶ (C ⟶[V] D) :=
    (Iso.eHomCongr V (α_ X.1.1.1 X.1.1.2 X.1.2) (α_ Y.1.1.1 Y.1.1.2 Y.1.2)).hom
  let u : (A ⟶[V] B) ⊗ R ⟶ (A ⊗ X.2) ⟶[V] (B ⊗ Y.2) := d.tensorMap A B X.2 Y.2
  let v : (C ⟶[V] D) ⊗ R ⟶ (C ⊗ X.2) ⟶[V] (D ⊗ Y.2) := d.tensorMap C D X.2 Y.2
  let q₄ : ((A ⊗ X.2) ⟶[V] (B ⊗ Y.2)) ⟶ ((C ⊗ X.2) ⟶[V] (D ⊗ Y.2)) :=
    (Iso.eHomCongr V ((α_ X.1.1.1 X.1.1.2 X.1.2) ⊗ᵢ Iso.refl X.2)
      ((α_ Y.1.1.1 Y.1.1.2 Y.1.2) ⊗ᵢ Iso.refl Y.2)).hom
  have hi : r = l ≫ q := AssociatorIndex.indexMap_congr d X.1 Y.1
  have ht : (q ⊗ₘ 𝟙 R) ≫ v = u ≫ q₄ := by
    simpa only [A, B, C, D, R, u, v, q, q₄, Iso.eHomCongr, Iso.refl_hom, Iso.refl_inv,
      eHomWhiskerRight_id, eHomWhiskerLeft_id, Category.id_comp] using
      tensor_congr d (α_ X.1.1.1 X.1.1.2 X.1.2) (α_ Y.1.1.1 Y.1.1.2 Y.1.2)
        (Iso.refl X.2) (Iso.refl Y.2)
  have hm : (l ≫ q) ⊗ₘ 𝟙 R = (l ⊗ₘ 𝟙 R) ≫ (q ⊗ₘ 𝟙 R) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  change (r ⊗ₘ 𝟙 R) ≫ v = ((l ⊗ₘ 𝟙 R) ≫ u) ≫ q₄
  rw [hi, hm, Category.assoc, ht]
  exact (Category.assoc _ _ _).symm


/-- Tensor the first index with the left-associated final three indices after the enriched
  product reassociation. -/
abbrev frontLeft : EnrichedFunctor V (indices (I := I)) I :=
  (front (V := V) (I := I)).comp V
    ((prodEnrichedFunctor (EnrichedFunctor.id V I) (AssociatorIndex.leftIndex d)).comp V
      d.tensorEnrichedFunctor)
/-- Tensor the first index with the right-associated final three indices after the
  enriched product reassociation. -/
abbrev frontRight : EnrichedFunctor V (indices (I := I)) I :=
  (front (V := V) (I := I)).comp V
    ((prodEnrichedFunctor (EnrichedFunctor.id V I) (AssociatorIndex.rightIndex d)).comp V
      d.tensorEnrichedFunctor)

/-- The original EC source uses the same full E index action. -/
theorem front_left_map (X Y : indices (I := I)) :
    (frontLeft d).map X Y = (indexE d).map X Y := by
  let R₁ : V := X.1.1.1 ⟶[V] Y.1.1.1
  let R₂ : V := X.1.1.2 ⟶[V] Y.1.1.2
  let R₃ : V := X.1.2 ⟶[V] Y.1.2
  let R₄ : V := X.2 ⟶[V] Y.2
  let R₂₃ : V := (X.1.1.2 ⊗ X.1.2) ⟶[V] (Y.1.1.2 ⊗ Y.1.2)
  let R₂₃₄ : V := ((X.1.1.2 ⊗ X.1.2) ⊗ X.2) ⟶[V] ((Y.1.1.2 ⊗ Y.1.2) ⊗ Y.2)
  let t : R₂ ⊗ R₃ ⟶ R₂₃ := d.tensorMap X.1.1.2 Y.1.1.2 X.1.2 Y.1.2
  let u : R₂₃ ⊗ R₄ ⟶ R₂₃₄ := d.tensorMap (X.1.1.2 ⊗ X.1.2) (Y.1.1.2 ⊗ Y.1.2) X.2 Y.2
  let v : R₁ ⊗ R₂₃₄ ⟶ (X.1.1.1 ⊗ ((X.1.1.2 ⊗ X.1.2) ⊗ X.2)) ⟶[V]
      (Y.1.1.1 ⊗ ((Y.1.1.2 ⊗ Y.1.2) ⊗ Y.2)) :=
    d.tensorMap X.1.1.1 Y.1.1.1 ((X.1.1.2 ⊗ X.1.2) ⊗ X.2) ((Y.1.1.2 ⊗ Y.1.2) ⊗ Y.2)
  change (((α_ R₁ R₂ R₃).hom ⊗ₘ 𝟙 R₄) ≫ (α_ R₁ (R₂ ⊗ R₃) R₄).hom) ≫
      ((𝟙 R₁ ⊗ₘ ((t ⊗ₘ 𝟙 R₄) ≫ u)) ≫ v) =
    (((α_ R₁ R₂ R₃).hom ≫ (𝟙 R₁ ⊗ₘ t)) ⊗ₘ 𝟙 R₄) ≫
      (α_ R₁ R₂₃ R₄).hom ≫ R₁ ◁ u ≫ v
  simp only [tensorHom_id, comp_whiskerRight, id_tensorHom, whiskerLeft_comp, Category.assoc]
  rw [associator_naturality_middle_assoc]

/-- The original EC target uses the same full C action; its product route is the actual Hom
  pentagon. -/
theorem front_right_map (X Y : indices (I := I)) :
    (frontRight d).map X Y = (indexC d).map X Y := by
  let R₁ : V := X.1.1.1 ⟶[V] Y.1.1.1
  let R₂ : V := X.1.1.2 ⟶[V] Y.1.1.2
  let R₃ : V := X.1.2 ⟶[V] Y.1.2
  let R₄ : V := X.2 ⟶[V] Y.2
  let R₃₄ : V := (X.1.2 ⊗ X.2) ⟶[V] (Y.1.2 ⊗ Y.2)
  let R₂₃₄ : V := (X.1.1.2 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] (Y.1.1.2 ⊗ (Y.1.2 ⊗ Y.2))
  let t : R₃ ⊗ R₄ ⟶ R₃₄ := d.tensorMap X.1.2 Y.1.2 X.2 Y.2
  let u : R₂ ⊗ R₃₄ ⟶ R₂₃₄ := d.tensorMap X.1.1.2 Y.1.1.2 (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)
  let v : R₁ ⊗ R₂₃₄ ⟶ (X.1.1.1 ⊗ (X.1.1.2 ⊗ (X.1.2 ⊗ X.2))) ⟶[V]
      (Y.1.1.1 ⊗ (Y.1.1.2 ⊗ (Y.1.2 ⊗ Y.2))) :=
    d.tensorMap X.1.1.1 Y.1.1.1 (X.1.1.2 ⊗ (X.1.2 ⊗ X.2)) (Y.1.1.2 ⊗ (Y.1.2 ⊗ Y.2))
  have hp : ((α_ R₁ R₂ R₃).hom ⊗ₘ 𝟙 R₄) ≫ (α_ R₁ (R₂ ⊗ R₃) R₄).hom ≫
      R₁ ◁ (α_ R₂ R₃ R₄).hom =
    (α_ (R₁ ⊗ R₂) R₃ R₄).hom ≫ (α_ R₁ R₂ (R₃ ⊗ R₄)).hom := by monoidal
  change (((α_ R₁ R₂ R₃).hom ⊗ₘ 𝟙 R₄) ≫ (α_ R₁ (R₂ ⊗ R₃) R₄).hom) ≫
      ((𝟙 R₁ ⊗ₘ ((α_ R₂ R₃ R₄).hom ≫ R₂ ◁ t ≫ u)) ≫ v) =
    ((α_ (R₁ ⊗ R₂) R₃ R₄).hom ≫ (𝟙 (R₁ ⊗ R₂) ⊗ₘ t)) ≫
      (α_ R₁ R₂ R₃₄).hom ≫ R₁ ◁ u ≫ v
  simp only [id_tensorHom, tensorHom_id, whiskerLeft_comp, Category.assoc]
  rw [associator_naturality_right_assoc]
  simpa only [Category.assoc, tensorHom_id] using
    congrArg (fun z => z ≫ R₁ ◁ R₂ ◁ t ≫ R₁ ◁ u ≫ v) hp

/-- EC acts on the entire original four-input Hom, retaining the positive coefficient associator
  only. -/
theorem edgeEC_map (X Y : indices (I := I)) :
    (indexC d).map X Y = (indexE d).map X Y ≫ (Iso.eHomCongr V (edgeEC d X) (edgeEC d Y)).hom := by
  let A : I := (X.1.1.2 ⊗ X.1.2) ⊗ X.2
  let B : I := (Y.1.1.2 ⊗ Y.1.2) ⊗ Y.2
  let C : I := X.1.1.2 ⊗ (X.1.2 ⊗ X.2)
  let D : I := Y.1.1.2 ⊗ (Y.1.2 ⊗ Y.2)
  let S : V := ((X.1.1.2 ⟶[V] Y.1.1.2) ⊗ (X.1.2 ⟶[V] Y.1.2)) ⊗ (X.2 ⟶[V] Y.2)
  let R : V := X.1.1.1 ⟶[V] Y.1.1.1
  let P : V := X ⟶[V] Y
  let t : P ⟶ R ⊗ S := (front (V := V) (I := I)).map X Y
  let l : S ⟶ (A ⟶[V] B) := (AssociatorIndex.leftIndex d).map ((X.1.1.2, X.1.2), X.2) ((Y.1.1.2,
    Y.1.2), Y.2)
  let r : S ⟶ (C ⟶[V] D) := (AssociatorIndex.rightIndex d).map ((X.1.1.2, X.1.2), X.2) ((Y.1.1.2,
    Y.1.2), Y.2)
  let q : (A ⟶[V] B) ⟶ (C ⟶[V] D) :=
    (Iso.eHomCongr V (α_ X.1.1.2 X.1.2 X.2) (α_ Y.1.1.2 Y.1.2 Y.2)).hom
  let u : R ⊗ (A ⟶[V] B) ⟶ (X.1.1.1 ⊗ A) ⟶[V] (Y.1.1.1 ⊗ B) := d.tensorMap X.1.1.1 Y.1.1.1 A B
  let v : R ⊗ (C ⟶[V] D) ⟶ (X.1.1.1 ⊗ C) ⟶[V] (Y.1.1.1 ⊗ D) := d.tensorMap X.1.1.1 Y.1.1.1 C D
  let q₄ : ((X.1.1.1 ⊗ A) ⟶[V] (Y.1.1.1 ⊗ B)) ⟶ ((X.1.1.1 ⊗ C) ⟶[V] (Y.1.1.1 ⊗ D)) :=
    (Iso.eHomCongr V (Iso.refl X.1.1.1 ⊗ᵢ (α_ X.1.1.2 X.1.2 X.2))
      (Iso.refl Y.1.1.1 ⊗ᵢ (α_ Y.1.1.2 Y.1.2 Y.2))).hom
  have hi : r = l ≫ q := AssociatorIndex.indexMap_congr d ((X.1.1.2, X.1.2), X.2) ((Y.1.1.2, Y.1.2),
    Y.2)
  have ht : (𝟙 R ⊗ₘ q) ≫ v = u ≫ q₄ := by
    simpa only [A, B, C, D, R, u, v, q, q₄, Iso.eHomCongr, Iso.refl_hom, Iso.refl_inv,
      eHomWhiskerRight_id, eHomWhiskerLeft_id, Category.id_comp] using
      tensor_congr d (Iso.refl X.1.1.1) (Iso.refl Y.1.1.1)
        (α_ X.1.1.2 X.1.2 X.2) (α_ Y.1.1.2 Y.1.2 Y.2)
  have hm : 𝟙 R ⊗ₘ (l ≫ q) = (𝟙 R ⊗ₘ l) ≫ (𝟙 R ⊗ₘ q) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  let outE : P ⟶ (X.1.1.1 ⊗ A) ⟶[V] (Y.1.1.1 ⊗ B) := (indexE d).map X Y
  let outC : P ⟶ (X.1.1.1 ⊗ C) ⟶[V] (Y.1.1.1 ⊗ D) := (indexC d).map X Y
  have hl : t ≫ (𝟙 R ⊗ₘ l) ≫ u = outE := front_left_map d X Y
  have hr : t ≫ (𝟙 R ⊗ₘ r) ≫ v = outC := front_right_map d X Y
  have hs : (𝟙 R ⊗ₘ r) ≫ v = (𝟙 R ⊗ₘ l) ≫ u ≫ q₄ := by
    rw [hi, hm, Category.assoc, ht]
  have h₀ := congrArg (fun z => t ≫ z) hs
  have h₁ := congrArg (fun z => z ≫ q₄) hl
  change outC = outE ≫ q₄
  have h₂ : t ≫ (𝟙 R ⊗ₘ r) ≫ v = t ≫ (𝟙 R ⊗ₘ l) ≫ u ≫ q₄ := by
    simpa only [Category.assoc] using h₀
  have h₃ : t ≫ (𝟙 R ⊗ₘ l) ≫ u ≫ q₄ = outE ≫ q₄ := by
    simpa only [Category.assoc] using h₁
  exact hr.symm.trans (h₂.trans h₃)

/-- The five actual positive index components satisfy the original index pentagon. -/
theorem edge_pentagon (X : indices (I := I)) :
    (edgeAB d X).hom ≫ (edgeBC d X).hom =
      (edgeAD d X).hom ≫ (edgeDE d X).hom ≫ (edgeEC d X).hom := by
  change (α_ (X.1.1.1 ⊗ X.1.1.2) X.1.2 X.2).hom ≫
      (α_ X.1.1.1 X.1.1.2 (X.1.2 ⊗ X.2)).hom =
    ((α_ X.1.1.1 X.1.1.2 X.1.2).hom ⊗ₘ 𝟙 X.2) ≫
      (α_ X.1.1.1 (X.1.1.2 ⊗ X.1.2) X.2).hom ≫
      (𝟙 X.1.1.1 ⊗ₘ (α_ X.1.1.2 X.1.2 X.2).hom)
  simp only [tensorHom_id, id_tensorHom]
  monoidal

end CategoryTheory.EnrichedDayKernel.AssociatorQuadIndex
