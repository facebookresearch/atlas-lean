/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ExcisiveTriad
public import MathlibExt.Topology.Category.TopPair.Product
public import MathlibExt.Topology.Category.TopPair.Range
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Excisive product unions of topological pairs

The two Cartesian-product axes of topological pairs define the product-union
excision condition. Open subspace ranges satisfy this condition, which is
identified with relative cup-product excision. Product-excisive pairs carry the
corresponding union comparison isomorphisms and natural projection maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace TopPair

def productAY (P Q : TopPair.{u}) :
    Set (P.fst ⊗ Q.fst : TopCat.{u}) :=
  Set.range P.map ×ˢ Set.univ

def productXB (P Q : TopPair.{u}) :
    Set (P.fst ⊗ Q.fst : TopCat.{u}) :=
  Set.univ ×ˢ Set.range Q.map

@[simp]
theorem mem_productAY (P Q : TopPair.{u})
    (x : (P.fst ⊗ Q.fst : TopCat.{u})) :
    x ∈ productAY P Q ↔ x.1 ∈ Set.range P.map := by
  change
    (x.1 ∈ Set.range P.map ∧ x.2 ∈ (Set.univ : Set Q.fst)) ↔ _
  simp

@[simp]
theorem mem_productXB (P Q : TopPair.{u})
    (x : (P.fst ⊗ Q.fst : TopCat.{u})) :
    x ∈ productXB P Q ↔ x.2 ∈ Set.range Q.map := by
  change
    (x.1 ∈ (Set.univ : Set P.fst) ∧
      x.2 ∈ Set.range Q.map) ↔ _
  simp

/-- Product pairs whose two subspace ranges are open satisfy product-union
excision. -/
theorem isProductUnionExcisive_of_isOpen_ranges
    (P Q : TopPair.{u})
    (hP : IsOpen (Set.range P.map)) (hQ : IsOpen (Set.range Q.map)) :
    IsProductUnionExcisive P Q := by
  have hXB : IsOpen (prodObjXB P Q) :=
    (isOpen_univ.prod hQ).preimage (prodObj P Q).map.hom.continuous
  have hAY : IsOpen (prodObjAY P Q) :=
    (hP.prod isOpen_univ).preimage (prodObj P Q).map.hom.continuous
  intro x _
  rw [hXB.interior_eq, hAY.interior_eq]
  rw [Set.mem_union, mem_prodObjXB, mem_prodObjAY]
  rcases Set.mem_unionProd.mp x.2 with hx | hx
  · exact Or.inr hx
  · exact Or.inl hx

/-- A pair with open subspace range satisfies product-union excision with
itself. -/
theorem isProductUnionExcisive_self_of_isOpen_range
    (P : TopPair.{u}) (hP : IsOpen (Set.range P.map)) :
    IsProductUnionExcisive P P :=
  isProductUnionExcisive_of_isOpen_ranges P P hP hP

theorem isProductUnionExcisive_iff_isRelativeCupExcisive
    (P Q : TopPair.{u}) :
    IsProductUnionExcisive P Q ↔
      AlgebraicTopology.IsRelativeCupExcisive
        (productAY P Q) (productXB P Q) := by
  unfold AlgebraicTopology.IsRelativeCupExcisive
    AlgebraicTopology.relativeCupLeft
    AlgebraicTopology.relativeCupRight
    AlgebraicTopology.relativeCupUnionSpace
  rw [show productAY P Q ∪ productXB P Q =
    productXB P Q ∪ productAY P Q from Set.union_comm _ _]
  change
    ((Set.univ : Set (prodObj P Q).snd) ⊆
      interior (prodObjXB P Q) ∪ interior (prodObjAY P Q)) ↔
    ((Set.univ : Set (prodObj P Q).snd) ⊆
      interior (prodObjAY P Q) ∪ interior (prodObjXB P Q))
  constructor <;> intro h x hx
  · rcases h hx with hxXB | hxAY
    · exact Or.inr hxXB
    · exact Or.inl hxAY
  · rcases h hx with hxAY | hxXB
    · exact Or.inr hxAY
    · exact Or.inl hxXB

def isProductExcisive :
    ObjectProperty (TopPair.{u} × TopPair.{u}) :=
  fun PQ => IsProductUnionExcisive PQ.1 PQ.2

abbrev ProductExcisivePair :=
  isProductExcisive.FullSubcategory

namespace ProductExcisivePair

abbrev inclusion :
    ProductExcisivePair.{u} ⥤ TopPair.{u} × TopPair.{u} :=
  ObjectProperty.ι isProductExcisive

noncomputable def triadFunctor :
    ProductExcisivePair.{u} ⥤
      AlgebraicTopology.ExcisiveTriad.{u} where
  obj T :=
    { X := T.obj.1.fst ⊗ T.obj.2.fst
      left := productAY T.obj.1 T.obj.2
      right := productXB T.obj.1 T.obj.2
      excisive :=
        (isProductUnionExcisive_iff_isRelativeCupExcisive _ _).mp
          T.property }
  map {S T} f :=
    { f := Hom.fst f.hom.1 ⊗ₘ Hom.fst f.hom.2
      left_maps := by
        intro x hx
        rw [mem_productAY] at hx ⊢
        change Hom.fst f.hom.1 x.1 ∈ Set.range T.obj.1.map
        rcases hx with ⟨a, ha⟩
        refine ⟨Hom.snd f.hom.1 a, ?_⟩
        calc
          T.obj.1.map (Hom.snd f.hom.1 a) =
              Hom.fst f.hom.1 (S.obj.1.map a) := by
            simpa only [TopCat.comp_app] using
              congrArg (fun k => k a) (Hom.w f.hom.1)
          _ = Hom.fst f.hom.1 x.1 :=
            congrArg (Hom.fst f.hom.1) ha
      right_maps := by
        intro x hx
        rw [mem_productXB] at hx ⊢
        change Hom.fst f.hom.2 x.2 ∈ Set.range T.obj.2.map
        rcases hx with ⟨b, hb⟩
        refine ⟨Hom.snd f.hom.2 b, ?_⟩
        calc
          T.obj.2.map (Hom.snd f.hom.2 b) =
              Hom.fst f.hom.2 (S.obj.2.map b) := by
            simpa only [TopCat.comp_app] using
              congrArg (fun k => k b) (Hom.w f.hom.2)
          _ = Hom.fst f.hom.2 x.2 :=
            congrArg (Hom.fst f.hom.2) hb }
  map_id T := by
    apply AlgebraicTopology.ExcisiveTriad.Hom.ext
    change
      (𝟙 T.obj.1.fst) ⊗ₘ (𝟙 T.obj.2.fst) =
        𝟙 (T.obj.1.fst ⊗ T.obj.2.fst)
    simp
  map_comp f g := by
    apply AlgebraicTopology.ExcisiveTriad.Hom.ext
    change
      (Hom.fst f.hom.1 ≫ Hom.fst g.hom.1) ⊗ₘ
          (Hom.fst f.hom.2 ≫ Hom.fst g.hom.2) =
        (Hom.fst f.hom.1 ⊗ₘ Hom.fst f.hom.2) ≫
          (Hom.fst g.hom.1 ⊗ₘ Hom.fst g.hom.2)
    simp

@[simp]
theorem triadFunctor_obj_X (T : ProductExcisivePair.{u}) :
    (triadFunctor.obj T).X =
      T.obj.1.fst ⊗ T.obj.2.fst := rfl

@[simp]
theorem triadFunctor_obj_left (T : ProductExcisivePair.{u}) :
    (triadFunctor.obj T).left =
      productAY T.obj.1 T.obj.2 := rfl

@[simp]
theorem triadFunctor_obj_right (T : ProductExcisivePair.{u}) :
    (triadFunctor.obj T).right =
      productXB T.obj.1 T.obj.2 := rfl

@[simp]
theorem triadFunctor_map_f
    {S T : ProductExcisivePair.{u}} (f : S ⟶ T) :
    (triadFunctor.map f).f =
      Hom.fst f.hom.1 ⊗ₘ Hom.fst f.hom.2 := rfl

noncomputable abbrev leftSupportFunctor :
    ProductExcisivePair.{u} ⥤ TopPair.{u} :=
  triadFunctor ⋙
    AlgebraicTopology.ExcisiveTriad.leftPairFunctor

noncomputable abbrev rightSupportFunctor :
    ProductExcisivePair.{u} ⥤ TopPair.{u} :=
  triadFunctor ⋙
    AlgebraicTopology.ExcisiveTriad.rightPairFunctor

noncomputable abbrev unionSupportFunctor :
    ProductExcisivePair.{u} ⥤ TopPair.{u} :=
  triadFunctor ⋙
    AlgebraicTopology.ExcisiveTriad.unionPairFunctor

abbrev leftFactorFunctor :
    ProductExcisivePair.{u} ⥤ TopPair.{u} :=
  inclusion ⋙ CategoryTheory.Prod.fst TopPair.{u} TopPair.{u}

abbrev rightFactorFunctor :
    ProductExcisivePair.{u} ⥤ TopPair.{u} :=
  inclusion ⋙ CategoryTheory.Prod.snd TopPair.{u} TopPair.{u}

noncomputable abbrev productFunctor :
    ProductExcisivePair.{u} ⥤ TopPair.{u} :=
  inclusion ⋙ MonoidalCategory.tensor TopPair.{u}

noncomputable def leftProjection :
    leftSupportFunctor ⟶ leftFactorFunctor where
  app T :=
    TopPair.ofSubsetMap
        (CartesianMonoidalCategory.fst T.obj.1.fst T.obj.2.fst)
        (fun x hx => (mem_productAY T.obj.1 T.obj.2 x).mp hx) ≫
      (TopPair.rangeIso T.obj.1).inv
  naturality S T f := by
    apply TopPair.proj₁.map_injective
    cat_disch

noncomputable def rightProjection :
    rightSupportFunctor ⟶ rightFactorFunctor where
  app T :=
    TopPair.ofSubsetMap
        (CartesianMonoidalCategory.snd T.obj.1.fst T.obj.2.fst)
        (fun x hx => (mem_productXB T.obj.1 T.obj.2 x).mp hx) ≫
      (TopPair.rangeIso T.obj.2).inv
  naturality S T f := by
    apply TopPair.proj₁.map_injective
    cat_disch

noncomputable def productCupUnionIso
    (T : ProductExcisivePair.{u}) :
    unionSupportFunctor.obj T ≅ productFunctor.obj T := by
  change
    TopPair.ofSubset
        (productAY T.obj.1 T.obj.2 ∪
          productXB T.obj.1 T.obj.2) ≅
      prodObj T.obj.1 T.obj.2
  let h :
      productAY T.obj.1 T.obj.2 ∪
          productXB T.obj.1 T.obj.2 =
        (Set.range T.obj.1.map).unionProd
          (Set.range T.obj.2.map) := by
    rw [show
      productAY T.obj.1 T.obj.2 ∪
          productXB T.obj.1 T.obj.2 =
        productXB T.obj.1 T.obj.2 ∪
          productAY T.obj.1 T.obj.2
      from Set.union_comm _ _]
    rfl
  exact CategoryTheory.MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (Homeomorph.setCongr h))
    (Iso.refl _)
    (by ext x; rfl)

noncomputable def unionProductNatIso :
    unionSupportFunctor ≅ productFunctor :=
  NatIso.ofComponents productCupUnionIso (fun f => by
    apply TopPair.proj₁.map_injective
    change
      (Hom.fst f.hom.1 ⊗ₘ Hom.fst f.hom.2) ≫ 𝟙 _ =
        𝟙 _ ≫
          (Hom.fst f.hom.1 ⊗ₘ Hom.fst f.hom.2)
    simp)

@[simp]
theorem leftProjection_app_fst (T : ProductExcisivePair.{u}) :
    Hom.fst (leftProjection.app T) =
      CartesianMonoidalCategory.fst
        T.obj.1.fst T.obj.2.fst := by
  change CartesianMonoidalCategory.fst _ _ ≫ 𝟙 _ = _
  simp
  rfl

@[simp]
theorem rightProjection_app_fst (T : ProductExcisivePair.{u}) :
    Hom.fst (rightProjection.app T) =
      CartesianMonoidalCategory.snd
        T.obj.1.fst T.obj.2.fst := by
  change CartesianMonoidalCategory.snd _ _ ≫ 𝟙 _ = _
  simp
  rfl

@[simp]
theorem productCupUnionIso_hom_fst
    (T : ProductExcisivePair.{u}) :
    Hom.fst (productCupUnionIso T).hom = 𝟙 _ := rfl

@[simp]
theorem productCupUnionIso_inv_fst
    (T : ProductExcisivePair.{u}) :
    Hom.fst (productCupUnionIso T).inv = 𝟙 _ := rfl

end ProductExcisivePair
end TopPair
