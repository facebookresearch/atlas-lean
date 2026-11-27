/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.ProperQuotientProduct
public import MathlibExt.Topology.Category.TopCat.ProdPushoutFactors
public import MathlibExt.Topology.Category.TopCat.PushoutOpenRestriction
public import MathlibExt.Topology.Category.TopCat.ProdPushoutQuotient
public import MathlibExt.Topology.Category.TopCat.ProdPushoutSymm

/-!
# Compact pushouts with arbitrary right product factors

Let X₁→X₂, X₁→X₃, X₂→X₄ and X₃→X₄ form a pushout. If X₂ and X₃ are compact and X₄ is Hausdorff,
taking a product with any space on the right preserves the square as a pushout.

The same conclusion holds for the square restricted over an open subset of X₄, under the
compactness and Hausdorff hypotheses on the original square. All spaces use an arbitrary
universe u.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace TopCat

private theorem isPushout_prodMap_right_of_isPushout_of_quotient
    {F X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b)
    (hqm : IsQuotientMap
      (Prod.map id (Sum.elim r b) :
        F × (X₂ ⊕ X₃) → F × X₄)) :
    IsPushout (prod.map t (𝟙 F)) (prod.map l (𝟙 F))
      (prod.map r (𝟙 F)) (prod.map b (𝟙 F)) := by
  have hcommProd : prod.map (𝟙 F) t ≫ prod.map (𝟙 F) r =
      prod.map (𝟙 F) l ≫ prod.map (𝟙 F) b := by
    rw [Limits.prod.map_map, Limits.prod.map_map, h.w]
  have hq :=
    TopCat.isQuotientMap_coprodDesc_prodMap_of_quotientProd hqm
  have hfac := TopCat.prodPushoutFactors_of_isPushout (K := F) h
  have hcolim :=
    TopCat.pushoutCoconeIsColimitOfIsQuotientMap
      (PushoutCocone.mk (prod.map (𝟙 F) r)
        (prod.map (𝟙 F) b) hcommProd) hq hfac
  exact TopCat.isPushout_prod_map_fixedRight_of_fixedLeft
    (IsPushout.of_isColimit hcolim)

private noncomputable def preimageSumHomeomorph
    {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] (r : C(A, C)) (b : C(B, C)) (U : Set C) :
    Set.preimage r U ⊕ Set.preimage b U ≃ₜ
      Set.preimage (Sum.elim r b) U := by
  let S : Set (A ⊕ B) := Set.preimage (Sum.elim r b) U
  let f : Set.preimage r U ⊕ Set.preimage b U → S :=
    Sum.elim (S.restrictPreimage Sum.inl)
      (S.restrictPreimage Sum.inr)
  have hleft : IsOpenEmbedding
      (S.restrictPreimage (Sum.inl : A → A ⊕ B)) :=
    Topology.IsOpenEmbedding.inl.restrictPreimage S
  have hright : IsOpenEmbedding
      (S.restrictPreimage (Sum.inr : B → A ⊕ B)) :=
    Topology.IsOpenEmbedding.inr.restrictPreimage S
  have hinj : Function.Injective f := by
    apply Function.Injective.sumElim hleft.injective hright.injective
    intro x y hxy
    have h := congrArg Subtype.val hxy
    cases h
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    cases z with
    | inl x => exact ⟨Sum.inl ⟨x, hz⟩, rfl⟩
    | inr x => exact ⟨Sum.inr ⟨x, hz⟩, rfl⟩
  exact IsHomeomorph.homeomorph f
    ⟨hleft.continuous.sumElim hright.continuous,
      hleft.isOpenMap.sumElim hright.isOpenMap, hinj, hsurj⟩

private theorem prod_preimage_eq (P : RestrictedPushout.{u})
    (F : TopCat.{u}) :
    Set.preimage
        (Prod.map id (Sum.elim P.r P.b) :
          F × (P.X₂ ⊕ P.X₃) → F × P.X₄)
        ((Set.univ : Set F) ×ˢ P.U) =
      (Set.univ : Set F) ×ˢ
        Set.preimage (Sum.elim P.r P.b) P.U := by
  ext z
  simp

private noncomputable def restrictedSourceHomeomorph
    (P : RestrictedPushout.{u}) (F : TopCat.{u}) :
    F × (P.obj₂ ⊕ P.obj₃) ≃ₜ
      Set.preimage
        (Prod.map id (Sum.elim P.r P.b) :
          F × (P.X₂ ⊕ P.X₃) → F × P.X₄)
        ((Set.univ : Set F) ×ˢ P.U) :=
  (Homeomorph.prodCongr (Homeomorph.refl F)
    (preimageSumHomeomorph P.r.hom P.b.hom P.U)).trans
    ((Homeomorph.prodCongr (Homeomorph.Set.univ F).symm
      (Homeomorph.refl _)).trans
      ((Homeomorph.Set.prod (Set.univ : Set F)
        (Set.preimage (Sum.elim P.r P.b) P.U)).symm.trans
        (Homeomorph.setCongr (prod_preimage_eq P F).symm)))

private noncomputable def restrictedTargetHomeomorph
    (P : RestrictedPushout.{u}) (F : TopCat.{u}) :
    ((Set.univ : Set F) ×ˢ P.U) ≃ₜ F × P.obj₄ :=
  (Homeomorph.Set.prod (Set.univ : Set F) P.U).trans
    (Homeomorph.prodCongr (Homeomorph.Set.univ F)
      (Homeomorph.refl _))

private theorem restricted_product_apply
    (P : RestrictedPushout.{u}) (F : TopCat.{u})
    (z : F × (P.obj₂ ⊕ P.obj₃)) :
    restrictedTargetHomeomorph P F
        (((Set.univ : Set F) ×ˢ P.U).restrictPreimage
          (Prod.map id (Sum.elim P.r P.b))
          (restrictedSourceHomeomorph P F z)) =
      Prod.map id (Sum.elim P.rU P.bU) z := by
  rcases z with ⟨f, z⟩
  cases z <;> rfl

/-- Let X₁→X₂, X₁→X₃, r:X₂→X₄ and b:X₃→X₄ form a pushout square in TopCat. If X₂,X₃ are compact and
X₄ Hausdorff, the four maps multiplied by id_F on the right form a pushout for every space F. -/
theorem isPushout_prodMap_right_of_isPushout_of_compact_to_t2
    {F X₁ X₂ X₃ X₄ : TopCat.{u}}
    [CompactSpace X₂] [CompactSpace X₃] [T2Space X₄]
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b) :
    IsPushout (prod.map t (𝟙 F)) (prod.map l (𝟙 F))
      (prod.map r (𝟙 F)) (prod.map b (𝟙 F)) := by
  have hq : IsQuotientMap
      (Sum.elim r b : X₂ ⊕ X₃ → X₄) :=
    TopCat.isQuotientMap_sumElim_of_isPushout h
  have hqm : IsQuotientMap
      (Prod.map id (Sum.elim r b) :
        F × (X₂ ⊕ X₃) → F × X₄) :=
    Topology.IsQuotientMap.prodMap_right_of_compact_to_t2
      hq.continuous hq.surjective
  exact isPushout_prodMap_right_of_isPushout_of_quotient h hqm

namespace RestrictedPushout

/-- For an exhibited pushout with compact X₂,X₃ and Hausdorff apex X₄, restrict the square over an
open U⊆X₄. Multiplying all four restricted maps on the right by any space F gives a pushout. -/
theorem isPushout_prodMap_right_of_compact_to_t2
    (P : TopCat.RestrictedPushout.{u})
    [CompactSpace P.X₂] [CompactSpace P.X₃] [T2Space P.X₄]
    (hU : IsOpen P.U) (F : TopCat.{u}) :
    IsPushout (prod.map P.tU (𝟙 F)) (prod.map P.lU (𝟙 F))
      (prod.map P.rU (𝟙 F)) (prod.map P.bU (𝟙 F)) := by
  let q : C(P.X₂ ⊕ P.X₃, P.X₄) :=
    ⟨Sum.elim P.r P.b,
      P.r.hom.continuous.sumElim P.b.hom.continuous⟩
  let qProd : C(F × (P.X₂ ⊕ P.X₃), F × P.X₄) :=
    ⟨Prod.map id q, continuous_id.prodMap q.continuous⟩
  let W : Set (F × P.X₄) := (Set.univ : Set F) ×ˢ P.U
  have hq : IsQuotientMap q :=
    TopCat.isQuotientMap_sumElim_of_isPushout P.h
  have hqProd : IsQuotientMap qProd :=
    Topology.IsQuotientMap.prodMap_right_of_compact_to_t2
      hq.continuous hq.surjective
  have hqOpen : IsQuotientMap (W.restrictPreimage qProd) :=
    hqProd.restrictPreimage_isOpen (isOpen_univ.prod hU)
  let eSrc := restrictedSourceHomeomorph P F
  let eTgt := restrictedTargetHomeomorph P F
  have hcomp : IsQuotientMap
      (fun z => eTgt (W.restrictPreimage qProd (eSrc z))) :=
    eTgt.isQuotientMap.comp (hqOpen.comp eSrc.isQuotientMap)
  have heq : (fun z => eTgt (W.restrictPreimage qProd (eSrc z))) =
      (Prod.map id (Sum.elim P.rU P.bU) :
        F × (P.obj₂ ⊕ P.obj₃) → F × P.obj₄) := by
    funext z
    exact restricted_product_apply P F z
  rw [heq] at hcomp
  exact isPushout_prodMap_right_of_isPushout_of_quotient
    (P.isPushout hU) hcomp

end RestrictedPushout

end TopCat
