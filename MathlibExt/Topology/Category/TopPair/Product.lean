/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.MorphismProperty.Arrow
public import MathlibExt.Data.Set.UnionProd
public import MathlibExt.Topology.Category.TopPair
public import MathlibExt.Topology.Category.TopCat.OrderedTwoSetCover
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# Products of topological pairs

The product of pairs `(X,A)` and `(Y,B)` has ambient space `X × Y` and subspace
`(X × B) ∪ (A × Y)`. These products define a symmetric monoidal structure whose
ambient projection preserves the braiding.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace TopPair

variable {P P' P'' Q Q' Q'' : TopPair.{u}}

/-- The ambient-space projection from topological pairs is faithful. -/
instance proj₁_faithful : TopPair.proj₁.Faithful :=
  MorphismProperty.Arrow.rightProjection_faithful _ _ _ fun {_ _} f hf =>
    (TopCat.mono_iff_injective f).2 hf.injective

@[simp]
lemma proj₁_map {P Q : TopPair.{u}} (f : P ⟶ Q) :
    TopPair.proj₁.map f = Hom.fst f := rfl

/-- The product of topological pairs `(X,A)` and `(Y,B)`, represented by the literal subset
`X × range(B → Y) ∪ range(A → X) × Y` of `X × Y`. -/
abbrev prodObj (P Q : TopPair.{u}) : TopPair.{u} :=
  TopPair.ofSubset (X := P.fst ⊗ Q.fst)
    ((Set.range P.map).unionProd (Set.range Q.map))

@[simp]
lemma prodObj_fst (P Q : TopPair.{u}) : (prodObj P Q).fst = P.fst ⊗ Q.fst := rfl

@[simp]
lemma prodObj_snd (P Q : TopPair.{u}) :
    (prodObj P Q).snd =
      TopCat.of ((Set.range P.map).unionProd (Set.range Q.map)) := rfl

@[simp]
lemma prodObj_map_apply (P Q : TopPair.{u}) (x : (prodObj P Q).snd) :
    (prodObj P Q).map x = x.1 := rfl

@[simp]
lemma range_prodObj_map (P Q : TopPair.{u}) :
    Set.range (prodObj P Q).map = (Set.range P.map).unionProd (Set.range Q.map) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

/-- The `X × B` piece, pulled back to the union subspace underlying the product pair. -/
def prodObjXB (P Q : TopPair.{u}) : Set (prodObj P Q).snd :=
  (prodObj P Q).map ⁻¹' ((Set.univ : Set P.fst) ×ˢ Set.range Q.map)

/-- The `A × Y` piece, pulled back to the union subspace underlying the product pair. -/
def prodObjAY (P Q : TopPair.{u}) : Set (prodObj P Q).snd :=
  (prodObj P Q).map ⁻¹' (Set.range P.map ×ˢ (Set.univ : Set Q.fst))

@[simp]
lemma mem_prodObjXB (P Q : TopPair.{u}) (x : (prodObj P Q).snd) :
    x ∈ prodObjXB P Q ↔ x.1.2 ∈ Set.range Q.map := by
  change (x.1.1 ∈ (Set.univ : Set P.fst) ∧
      x.1.2 ∈ Set.range Q.map) ↔ x.1.2 ∈ Set.range Q.map
  simp

@[simp]
lemma mem_prodObjAY (P Q : TopPair.{u}) (x : (prodObj P Q).snd) :
    x ∈ prodObjAY P Q ↔ x.1.1 ∈ Set.range P.map := by
  change (x.1.1 ∈ Set.range P.map ∧
      x.1.2 ∈ (Set.univ : Set Q.fst)) ↔ x.1.1 ∈ Set.range P.map
  simp

/-- The exact excision hypothesis for the two pieces of a product-pair union.
The interiors are taken in the union subspace, not in the ambient product. -/
def IsProductUnionExcisive (P Q : TopPair.{u}) : Prop :=
  (Set.univ : Set (prodObj P Q).snd) ⊆
    interior (prodObjXB P Q) ∪ interior (prodObjAY P Q)

/-- The accepted ordered two-set cover attached to an excisive product-pair union. -/
def productUnionOrderedTwoSetCover (P Q : TopPair.{u})
    (h : IsProductUnionExcisive P Q) :
    AlgebraicTopology.OrderedTwoSetCover.{u} where
  X := (prodObj P Q).snd
  left := prodObjXB P Q
  right := prodObjAY P Q
  interior_cover := h

/-- The product of two morphisms of topological pairs. -/
def prodMap (f : P ⟶ P') (g : Q ⟶ Q') : prodObj P Q ⟶ prodObj P' Q' :=
  TopPair.ofHom (Hom.fst f ⊗ₘ Hom.fst g)
    (TopCat.ofHom
      { toFun := Set.codRestrict
          (fun x : (prodObj P Q).snd => (Hom.fst f x.1.1, Hom.fst g x.1.2))
          ((Set.range P'.map).unionProd (Set.range Q'.map))
          (fun x => by
            have hf : Set.MapsTo (Hom.fst f) (Set.range P.map) (Set.range P'.map) := by
              rintro _ ⟨a, rfl⟩
              refine ⟨Hom.snd f a, ?_⟩
              simpa only [TopCat.comp_app] using
                congrArg (fun k : P.snd ⟶ P'.fst => k a) (Hom.w f)
            have hg : Set.MapsTo (Hom.fst g) (Set.range Q.map) (Set.range Q'.map) := by
              rintro _ ⟨b, rfl⟩
              refine ⟨Hom.snd g b, ?_⟩
              simpa only [TopCat.comp_app] using
                congrArg (fun k : Q.snd ⟶ Q'.fst => k b) (Hom.w g)
            exact hf.unionProd hg x.2)
        continuous_toFun :=
          (((prodObj P Q).map ≫ (Hom.fst f ⊗ₘ Hom.fst g)).hom.continuous).codRestrict _ })
    (by ext x; rfl)

@[simp]
lemma prodMap_fst (f : P ⟶ P') (g : Q ⟶ Q') :
    Hom.fst (prodMap f g) = Hom.fst f ⊗ₘ Hom.fst g := rfl

lemma prodMap_snd_mapsTo_prodObjXB (f : P ⟶ P') (g : Q ⟶ Q') :
    Set.MapsTo (Hom.snd (prodMap f g)) (prodObjXB P Q) (prodObjXB P' Q') := by
  intro x hx
  rw [mem_prodObjXB] at hx
  rw [mem_prodObjXB]
  change Hom.fst g x.1.2 ∈ Set.range Q'.map
  rcases hx with ⟨b, hb⟩
  refine ⟨Hom.snd g b, ?_⟩
  calc
    Q'.map (Hom.snd g b) = Hom.fst g (Q.map b) := by
      simpa only [TopCat.comp_app] using
        congrArg (fun k : Q.snd ⟶ Q'.fst => k b) (Hom.w g)
    _ = Hom.fst g x.1.2 := congrArg (Hom.fst g) hb

lemma prodMap_snd_mapsTo_prodObjAY (f : P ⟶ P') (g : Q ⟶ Q') :
    Set.MapsTo (Hom.snd (prodMap f g)) (prodObjAY P Q) (prodObjAY P' Q') := by
  intro x hx
  rw [mem_prodObjAY] at hx
  rw [mem_prodObjAY]
  change Hom.fst f x.1.1 ∈ Set.range P'.map
  rcases hx with ⟨a, ha⟩
  refine ⟨Hom.snd f a, ?_⟩
  calc
    P'.map (Hom.snd f a) = Hom.fst f (P.map a) := by
      simpa only [TopCat.comp_app] using
        congrArg (fun k : P.snd ⟶ P'.fst => k a) (Hom.w f)
    _ = Hom.fst f x.1.1 := congrArg (Hom.fst f) ha

/-- Product maps induce morphisms between the canonical ordered product-union covers. -/
def productUnionOrderedTwoSetCoverMap (f : P ⟶ P') (g : Q ⟶ Q')
    (h : IsProductUnionExcisive P Q) (h' : IsProductUnionExcisive P' Q') :
    productUnionOrderedTwoSetCover P Q h ⟶
      productUnionOrderedTwoSetCover P' Q' h' where
  f := Hom.snd (prodMap f g)
  left_maps := prodMap_snd_mapsTo_prodObjXB f g
  right_maps := prodMap_snd_mapsTo_prodObjAY f g

@[simp]
lemma prodMap_id (P Q : TopPair.{u}) :
    prodMap (𝟙 P) (𝟙 Q) = 𝟙 (prodObj P Q) := by
  apply TopPair.proj₁.map_injective
  change 𝟙 P.fst ⊗ₘ 𝟙 Q.fst = 𝟙 (P.fst ⊗ Q.fst)
  simp

@[simp]
lemma prodMap_comp (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    prodMap (f ≫ f') (g ≫ g') = prodMap f g ≫ prodMap f' g' := by
  apply TopPair.proj₁.map_injective
  change (Hom.fst f ≫ Hom.fst f') ⊗ₘ (Hom.fst g ≫ Hom.fst g') =
    (Hom.fst f ⊗ₘ Hom.fst g) ≫ (Hom.fst f' ⊗ₘ Hom.fst g')
  simp

/-- The tensor unit topological pair. -/
abbrev unitObj : TopPair.{u} := TopPair.ofSubset (∅ : Set (𝟙_ TopCat.{u}))

/-- The product associator for topological pairs. -/
noncomputable def prodAssociator (P Q R : TopPair.{u}) :
    prodObj (prodObj P Q) R ≅ prodObj P (prodObj Q R) :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      ((TopCat.homeoOfIso (α_ P.fst Q.fst R.fst)).sets (by
        simp only [range_prodObj_map]
        change ((Set.range P.map).unionProd (Set.range Q.map)).unionProd
            (Set.range R.map) =
          Equiv.prodAssoc P.fst Q.fst R.fst ⁻¹'
            (Set.range P.map).unionProd
              ((Set.range Q.map).unionProd (Set.range R.map))
        exact (Set.prodAssoc_preimage_unionProd
          (Set.range P.map) (Set.range Q.map) (Set.range R.map)).symm)))
    (α_ P.fst Q.fst R.fst) (by ext x; rfl)

/-- The left unitor for products of topological pairs. -/
noncomputable def prodLeftUnitor (P : TopPair.{u}) : prodObj unitObj P ≅ P :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      (((TopCat.homeoOfIso (λ_ P.fst)).sets (by
          ext ⟨x, y⟩
          rw [Set.mem_unionProd (x := (x, y))]
          change _ ↔ y ∈ Set.range P.map
          constructor
          · rintro (h | h)
            · rcases h with ⟨a, _⟩
              exact a.2.elim
            · exact h
          · exact Or.inr)).trans
        P.isEmbedding_map.toHomeomorph.symm))
    (λ_ P.fst) (by
      ext x
      have hx : x.1.2 ∈ Set.range P.map := by
        rcases (Set.mem_unionProd (x := x.1)).1 x.2 with h | h
        · rcases h with ⟨a, _⟩
          exact a.2.elim
        · exact h
      let y : Set.range P.map := ⟨x.1.2, hx⟩
      change P.map (P.isEmbedding_map.toHomeomorph.symm y) = y.1
      exact congrArg Subtype.val (P.isEmbedding_map.toHomeomorph.apply_symm_apply y))

/-- The right unitor for products of topological pairs. -/
noncomputable def prodRightUnitor (P : TopPair.{u}) : prodObj P unitObj ≅ P :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      (((TopCat.homeoOfIso (ρ_ P.fst)).sets (by
          ext ⟨x, y⟩
          rw [Set.mem_unionProd (x := (x, y))]
          change _ ↔ x ∈ Set.range P.map
          constructor
          · rintro (h | h)
            · exact h
            · rcases h with ⟨a, _⟩
              exact a.2.elim
          · exact Or.inl)).trans
        P.isEmbedding_map.toHomeomorph.symm))
    (ρ_ P.fst) (by
      ext x
      have hx : x.1.1 ∈ Set.range P.map := by
        rcases (Set.mem_unionProd (x := x.1)).1 x.2 with h | h
        · exact h
        · rcases h with ⟨a, _⟩
          exact a.2.elim
      let y : Set.range P.map := ⟨x.1.1, hx⟩
      change P.map (P.isEmbedding_map.toHomeomorph.symm y) = y.1
      exact congrArg Subtype.val (P.isEmbedding_map.toHomeomorph.apply_symm_apply y))

/-- The braiding for products of topological pairs. -/
noncomputable def prodBraiding (P Q : TopPair.{u}) : prodObj P Q ≅ prodObj Q P :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      ((TopCat.homeoOfIso (β_ P.fst Q.fst)).sets (by
        change (Set.range P.map).unionProd (Set.range Q.map) =
          Equiv.prodComm P.fst Q.fst ⁻¹'
            (Set.range Q.map).unionProd (Set.range P.map)
        exact (Set.prodComm_preimage_unionProd
          (Set.range P.map) (Set.range Q.map)).symm)))
    (β_ P.fst Q.fst) (by ext x; rfl)

@[simp]
lemma prodAssociator_hom_fst (P Q R : TopPair.{u}) :
    Hom.fst (prodAssociator P Q R).hom = (α_ P.fst Q.fst R.fst).hom := rfl

@[simp]
lemma prodLeftUnitor_hom_fst (P : TopPair.{u}) :
    Hom.fst (prodLeftUnitor P).hom = (λ_ P.fst).hom := rfl

@[simp]
lemma prodRightUnitor_hom_fst (P : TopPair.{u}) :
    Hom.fst (prodRightUnitor P).hom = (ρ_ P.fst).hom := rfl

@[simp]
lemma prodBraiding_hom_fst (P Q : TopPair.{u}) :
    Hom.fst (prodBraiding P Q).hom = (β_ P.fst Q.fst).hom := rfl

/-- The product data on topological pairs. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct TopPair.{u} where
  tensorObj := prodObj
  whiskerLeft P _ _ g := prodMap (𝟙 P) g
  whiskerRight f Q := prodMap f (𝟙 Q)
  tensorHom := prodMap
  tensorUnit := unitObj
  associator := prodAssociator
  leftUnitor := prodLeftUnitor
  rightUnitor := prodRightUnitor

/-- Coherence data exhibiting the ambient projection as strictly preserving the chosen product
objects and structure maps. -/
noncomputable def proj₁InducingData :
    CategoryTheory.Monoidal.InducingFunctorData TopPair.proj₁ where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by
    intro X Y₁ Y₂ f
    change (𝟙 X.fst ⊗ₘ Hom.fst f) = 𝟙 _ ≫ (X.fst ◁ Hom.fst f) ≫ 𝟙 _
    simp
  whiskerRight_eq := by
    intro X₁ X₂ f Y
    change (Hom.fst f ⊗ₘ 𝟙 Y.fst) = 𝟙 _ ≫ (Hom.fst f ▷ Y.fst) ≫ 𝟙 _
    simp
  tensorHom_eq := by
    intro X₁ Y₁ X₂ Y₂ f g
    change (Hom.fst f ⊗ₘ Hom.fst g) = 𝟙 _ ≫ (Hom.fst f ⊗ₘ Hom.fst g) ≫ 𝟙 _
    simp
  associator_eq := by
    intro X Y Z
    change (α_ X.fst Y.fst Z.fst).hom = _
    cat_disch
  leftUnitor_eq := by
    intro X
    change (λ_ X.fst).hom = _
    cat_disch
  rightUnitor_eq := by
    intro X
    change (ρ_ X.fst).hom = _
    cat_disch

/-- The monoidal category structure on topological pairs induced from `TopCat`. -/
noncomputable instance monoidalCategory : MonoidalCategory TopPair.{u} :=
  CategoryTheory.Monoidal.induced TopPair.proj₁ proj₁InducingData

/-- The ambient projection is a strong monoidal functor. -/
noncomputable instance proj₁_monoidal : TopPair.proj₁.Monoidal :=
  (CategoryTheory.Monoidal.fromInducedCoreMonoidal TopPair.proj₁ proj₁InducingData).toMonoidal

/-- The braided structure on topological pairs induced from the product swap in `TopCat`. -/
noncomputable instance braidedCategory : BraidedCategory TopPair.{u} :=
  BraidedCategory.ofFaithful TopPair.proj₁ prodBraiding (by
    intro X Y
    change 𝟙 _ ≫ (β_ X.fst Y.fst).hom = (β_ X.fst Y.fst).hom ≫ 𝟙 _
    simp)

/-- The ambient projection preserves the braiding. -/
noncomputable instance proj₁_braided : TopPair.proj₁.Braided where
  braided X Y := by
    change 𝟙 _ ≫ (β_ X.fst Y.fst).hom = (β_ X.fst Y.fst).hom ≫ 𝟙 _
    simp

/-- The product braiding on topological pairs is symmetric. -/
noncomputable instance symmetricCategory : SymmetricCategory TopPair.{u} :=
  SymmetricCategory.ofFaithful TopPair.proj₁

end TopPair
