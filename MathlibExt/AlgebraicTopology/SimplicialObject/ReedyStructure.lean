/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyClasses
public import MathlibExt.CategoryTheory.Reedy.Corner
public import Mathlib.AlgebraicTopology.Reedy.SimplexCategory

/-!
# The Reedy structure of simplicial objects

Simplicial objects in `C` are functors `SimplexCategoryᵒᵖ ⥤ C`, and `SimplexCategoryᵒᵖ` carries the
Reedy structure opposite to Mathlib's Reedy structure on the simplex category: direct maps are the
opposites of epimorphisms, inverse maps the opposites of monomorphisms, and the degree of `⦋n⦌` is
`n`. This file compares the generic latching and matching data of that Reedy structure with the
simplicial latching and matching objects of `Latching` and `Matching`.

* The generic latching and matching categories of `op ⦋n⦌` are equivalent to `latchingIndex n` and
  `matchingIndex n`, compatibly with the diagrams of a simplicial object, so the generic shapes have
  (co)limits whenever the simplicial ones do.
* Under these equivalences the generic latching and matching maps are the simplicial ones, and the
  generic relative latching and matching corners are isomorphic, as arrows, to
  `relativeLatchingMap` and `relativeMatchingMap`.
* Hence `reedyLeft P` and `reedyRight Q` are the generic Reedy classes `latchingClass P` and
  `matchingClass Q` whenever `P` and `Q` respect isomorphisms, and they are stable under retracts
  whenever `P` and `Q` are.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- The Reedy structure of `SimplexCategoryᵒᵖ`, opposite to Mathlib's Reedy structure on the
simplex category. -/
abbrev reedyStructure : CategoryTheory.ReedyStructure SimplexCategoryᵒᵖ ℕ :=
  CategoryTheory.ReedyStructure.ofCanonical SimplexCategory.reedyStructure.op

theorem reedyStructure_degree (a : SimplexCategoryᵒᵖ) :
    reedyStructure.degree a = a.unop.len :=
  rfl

theorem reedyStructure_direct_iff {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    reedyStructure.direct f ↔ Epi f.unop :=
  Iff.rfl

theorem reedyStructure_inverse_iff {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    reedyStructure.inverse f ↔ Mono f.unop :=
  Iff.rfl

/-- The generic latching category of `op ⦋n⦌` presented as the simplicial latching index. -/
def latchingIndexOfReedy (n : ℕ) :
    reedyStructure.Latching (op ⦋n⦌) ⥤ latchingIndex n where
  obj a := ⟨CostructuredArrow.mk (reedyStructure.latchingArrow a),
    reedyStructure.latchingArrow_mem a, a.property⟩
  map f := ObjectProperty.homMk (CostructuredArrow.homMk
    (reedyStructure.latchingComparison f) (reedyStructure.latchingComparison_arrow f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The simplicial latching index presented as the generic latching category of `op ⦋n⦌`. -/
def reedyOfLatchingIndex (n : ℕ) :
    latchingIndex n ⥤ reedyStructure.Latching (op ⦋n⦌) where
  obj a := reedyStructure.latchingMk a.obj.hom a.property.1 a.property.2
  map {a b} f := by
    have hdirect : reedyStructure.direct f.hom.left := by
      change Epi f.hom.left.unop
      have hfac := congrArg Quiver.Hom.unop (CostructuredArrow.w f.hom)
      change b.obj.hom.unop ≫ f.hom.left.unop = a.obj.hom.unop at hfac
      let _ : Epi (b.obj.hom.unop ≫ f.hom.left.unop) := hfac.symm ▸ a.property.1
      exact epi_of_epi b.obj.hom.unop f.hom.left.unop
    exact ObjectProperty.homMk (Over.homMk ⟨f.hom.left, hdirect⟩ (by
      apply WideSubcategory.hom_ext
      exact CostructuredArrow.w f.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The generic latching category of `op ⦋n⦌` is the simplicial latching index. -/
def latchingEquivalence (n : ℕ) :
    reedyStructure.Latching (op ⦋n⦌) ≌ latchingIndex n where
  functor := latchingIndexOfReedy n
  inverse := reedyOfLatchingIndex n
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    simp only [Iso.refl_hom]
    rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    simp only [Iso.refl_hom]
    rfl)

/-- The generic matching category of `op ⦋n⦌` presented as the simplicial matching index. -/
def matchingIndexOfReedy (n : ℕ) :
    reedyStructure.Matching (op ⦋n⦌) ⥤ matchingIndex n where
  obj a := ⟨StructuredArrow.mk (reedyStructure.matchingArrow a),
    reedyStructure.matchingArrow_mem a, a.property⟩
  map f := ObjectProperty.homMk (StructuredArrow.homMk
    (reedyStructure.matchingComparison f) (reedyStructure.matchingArrow_comparison f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The simplicial matching index presented as the generic matching category of `op ⦋n⦌`. -/
def reedyOfMatchingIndex (n : ℕ) :
    matchingIndex n ⥤ reedyStructure.Matching (op ⦋n⦌) where
  obj a := reedyStructure.matchingMk a.obj.hom a.property.1 a.property.2
  map {a b} f := by
    have hinverse : reedyStructure.inverse f.hom.right := by
      change Mono f.hom.right.unop
      have hfac := congrArg Quiver.Hom.unop (StructuredArrow.w f.hom)
      change f.hom.right.unop ≫ a.obj.hom.unop = b.obj.hom.unop at hfac
      let _ : Mono (f.hom.right.unop ≫ a.obj.hom.unop) := hfac.symm ▸ b.property.1
      exact mono_of_mono f.hom.right.unop a.obj.hom.unop
    exact ObjectProperty.homMk (Under.homMk ⟨f.hom.right, hinverse⟩ (by
      apply WideSubcategory.hom_ext
      exact StructuredArrow.w f.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The generic matching category of `op ⦋n⦌` is the simplicial matching index. -/
def matchingEquivalence (n : ℕ) :
    reedyStructure.Matching (op ⦋n⦌) ≌ matchingIndex n where
  functor := matchingIndexOfReedy n
  inverse := reedyOfMatchingIndex n
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    simp only [Iso.refl_hom]
    rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    simp only [Iso.refl_hom]
    rfl)

variable {C : Type u} [Category.{v} C]

/-- The generic latching diagram of a simplicial object is its simplicial latching diagram. -/
theorem latchingIndexOfReedy_comp_latchingDiagram (X : SimplicialObject C) (n : ℕ) :
    latchingIndexOfReedy n ⋙ latchingDiagram X n = reedyStructure.latchingDiagram X (op ⦋n⦌) :=
  rfl

/-- The generic matching diagram of a simplicial object is its simplicial matching diagram. -/
theorem matchingIndexOfReedy_comp_matchingDiagram (X : SimplicialObject C) (n : ℕ) :
    matchingIndexOfReedy n ⋙ matchingDiagram X n = reedyStructure.matchingDiagram X (op ⦋n⦌) :=
  rfl

instance reedyStructure_hasLatchingColimits
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C] :
    ∀ a, HasColimitsOfShape (reedyStructure.Latching a) C :=
  fun a => hasColimitsOfShape_of_equivalence (latchingEquivalence a.unop.len).symm

instance reedyStructure_hasMatchingLimits
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C] :
    ∀ a, HasLimitsOfShape (reedyStructure.Matching a) C :=
  fun a => hasLimitsOfShape_of_equivalence (matchingEquivalence a.unop.len).symm

section Latching

variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]

/-- The generic latching object of `op ⦋n⦌` is the simplicial latching object. -/
def latchingObjectIso (X : SimplicialObject C) (n : ℕ) :
    colimit (reedyStructure.latchingDiagram X (op ⦋n⦌)) ≅ latchingObject X n :=
  HasColimit.isoOfEquivalence (latchingEquivalence n) (Iso.refl _)

@[reassoc]
theorem ι_latchingObjectIso_hom (X : SimplicialObject C) (n : ℕ)
    (a : reedyStructure.Latching (op ⦋n⦌)) :
    colimit.ι (reedyStructure.latchingDiagram X (op ⦋n⦌)) a ≫ (latchingObjectIso X n).hom =
      latchingι X n ((latchingIndexOfReedy n).obj a) := by
  unfold latchingObjectIso
  rw [HasColimit.ι_isoOfEquivalence_hom]
  simp only [Functor.comp_obj, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp]
  rfl

/-- The generic latching map is the simplicial one. -/
theorem reedyStructure_latchingMap_eq (X : SimplicialObject C) (n : ℕ) :
    reedyStructure.latchingMap X (op ⦋n⦌) = (latchingObjectIso X n).hom ≫ latchingMap X n := by
  apply colimit.hom_ext
  intro a
  rw [CategoryTheory.ReedyStructure.latchingMap_ι, ← Category.assoc,
    ι_latchingObjectIso_hom, latchingMap_ι]
  rfl

/-- The generic comparison of latching objects is the simplicial one. -/
theorem latchingObjectIso_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    colimMap (reedyStructure.latchingTransformation f (op ⦋n⦌)) ≫ (latchingObjectIso Y n).hom =
      (latchingObjectIso X n).hom ≫ (latchingObjectFunctor n).map f := by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, ι_colimMap, Category.assoc, ι_latchingObjectIso_hom,
    ← Category.assoc, ι_latchingObjectIso_hom, latchingObjectFunctor_map_ι]
  rfl

variable [HasPushouts C]

/-- The generic relative latching corner of `op ⦋n⦌` is, as an arrow, the relative latching map. -/
def latchingCornerArrowIso {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    Arrow.mk (reedyStructure.latchingCorner f (op ⦋n⦌)) ≅ Arrow.mk (relativeLatchingMap f n) := by
  let sourceMap := pushout.map
    (reedyStructure.latchingMap X (op ⦋n⦌))
    (colimMap (reedyStructure.latchingTransformation f (op ⦋n⦌)))
    (latchingMap X n) ((latchingObjectFunctor n).map f)
    (𝟙 _) (latchingObjectIso Y n).hom (latchingObjectIso X n).hom
    (by simpa using reedyStructure_latchingMap_eq X n) (latchingObjectIso_naturality f n)
  let _ : IsIso sourceMap := by
    dsimp [sourceMap]
    infer_instance
  refine Arrow.isoMk (asIso sourceMap) (Iso.refl _) ?_
  change sourceMap ≫ relativeLatchingMap f n =
    reedyStructure.latchingCorner f (op ⦋n⦌) ≫ 𝟙 _
  rw [Category.comp_id]
  apply pushout.hom_ext
  · dsimp [sourceMap, pushout.map]
    erw [pushout.inl_desc_assoc, Category.id_comp, relativeLatchingMap_inl,
      CategoryTheory.ReedyStructure.latchingCorner_inl]
  · dsimp [sourceMap, pushout.map]
    erw [pushout.inr_desc_assoc, Category.assoc, relativeLatchingMap_inr,
      CategoryTheory.ReedyStructure.latchingCorner_inr]
    exact (reedyStructure_latchingMap_eq Y n).symm

/-- `reedyLeft P` is the generic latching class of `P` when `P` respects isomorphisms. -/
theorem reedyLeft_eq_latchingClass (P : MorphismProperty C) [P.RespectsIso] :
    reedyLeft P = reedyStructure.latchingClass P := by
  ext X Y f
  constructor
  · intro hf a
    exact (P.arrow_mk_iso_iff (latchingCornerArrowIso f a.unop.len)).2 (hf a.unop.len)
  · intro hf n
    exact (P.arrow_mk_iso_iff (latchingCornerArrowIso f n)).1 (hf (op ⦋n⦌))

/-- `reedyLeft P` is stable under retracts whenever `P` is, as the generic latching class. -/
instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    (reedyLeft P).IsStableUnderRetracts := by
  rw [reedyLeft_eq_latchingClass]
  infer_instance

end Latching

section Matching

variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]

/-- The generic matching object of `op ⦋n⦌` is the simplicial matching object. -/
def matchingObjectIso (X : SimplicialObject C) (n : ℕ) :
    limit (reedyStructure.matchingDiagram X (op ⦋n⦌)) ≅ matchingObject X n :=
  HasLimit.isoOfEquivalence (matchingEquivalence n) (Iso.refl _)

@[reassoc]
theorem matchingObjectIso_hom_π (X : SimplicialObject C) (n : ℕ) (a : matchingIndex n) :
    (matchingObjectIso X n).hom ≫ matchingπ X n a =
      limit.π (reedyStructure.matchingDiagram X (op ⦋n⦌)) ((reedyOfMatchingIndex n).obj a) := by
  unfold matchingObjectIso matchingπ
  erw [HasLimit.isoOfEquivalence_hom_π]
  simp only [Functor.id_obj, Functor.comp_obj, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp]
  change _ ≫ ((matchingDiagramFunctor n).obj X).map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

/-- The generic matching map is the simplicial one. -/
theorem reedyStructure_matchingMap_comp (X : SimplicialObject C) (n : ℕ) :
    reedyStructure.matchingMap X (op ⦋n⦌) ≫ (matchingObjectIso X n).hom = matchingMap X n := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, matchingObjectIso_hom_π, CategoryTheory.ReedyStructure.matchingMap_π,
    matchingMap_π]
  rfl

/-- The generic comparison of matching objects is the simplicial one. -/
theorem matchingObjectIso_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    limMap (reedyStructure.matchingTransformation f (op ⦋n⦌)) ≫ (matchingObjectIso Y n).hom =
      (matchingObjectIso X n).hom ≫ (matchingObjectFunctor n).map f := by
  apply limit.hom_ext
  intro a
  erw [Category.assoc, matchingObjectIso_hom_π, limMap_π, Category.assoc,
    matchingObjectFunctor_map_π, ← Category.assoc, matchingObjectIso_hom_π]
  rfl

variable [HasPullbacks C]

/-- The generic relative matching corner of `op ⦋n⦌` is, as an arrow, the relative matching map;
the two pullbacks list their factors in opposite orders. -/
def matchingCornerArrowIso {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    Arrow.mk (reedyStructure.matchingCorner f (op ⦋n⦌)) ≅ Arrow.mk (relativeMatchingMap f n) := by
  let targetMap := pullback.map
    (limMap (reedyStructure.matchingTransformation f (op ⦋n⦌)))
    (reedyStructure.matchingMap Y (op ⦋n⦌))
    ((matchingObjectFunctor n).map f) (matchingMap Y n)
    (matchingObjectIso X n).hom (𝟙 _) (matchingObjectIso Y n).hom
    (matchingObjectIso_naturality f n) (by simpa using reedyStructure_matchingMap_comp Y n)
  let _ : IsIso targetMap := by
    dsimp [targetMap]
    infer_instance
  let targetIso := asIso targetMap ≪≫
    pullbackSymmetry ((matchingObjectFunctor n).map f) (matchingMap Y n)
  refine Arrow.isoMk (Iso.refl _) targetIso ?_
  change 𝟙 _ ≫ relativeMatchingMap f n =
    reedyStructure.matchingCorner f (op ⦋n⦌) ≫ targetMap ≫
      (pullbackSymmetry ((matchingObjectFunctor n).map f) (matchingMap Y n)).hom
  rw [Category.id_comp]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst]
    dsimp [targetMap, pullback.map]
    erw [pullback.lift_snd, Category.comp_id,
      CategoryTheory.ReedyStructure.matchingCorner_snd, relativeMatchingMap_fst]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd]
    dsimp [targetMap, pullback.map]
    erw [pullback.lift_fst, ← Category.assoc, CategoryTheory.ReedyStructure.matchingCorner_fst,
      relativeMatchingMap_snd]
    exact (reedyStructure_matchingMap_comp X n).symm

/-- `reedyRight Q` is the generic matching class of `Q` when `Q` respects isomorphisms. -/
theorem reedyRight_eq_matchingClass (Q : MorphismProperty C) [Q.RespectsIso] :
    reedyRight Q = reedyStructure.matchingClass Q := by
  ext X Y f
  constructor
  · intro hf a
    exact (Q.arrow_mk_iso_iff (matchingCornerArrowIso f a.unop.len)).2 (hf a.unop.len)
  · intro hf n
    exact (Q.arrow_mk_iso_iff (matchingCornerArrowIso f n)).1 (hf (op ⦋n⦌))

/-- `reedyRight Q` is stable under retracts whenever `Q` is, as the generic matching class. -/
instance (Q : MorphismProperty C) [Q.IsStableUnderRetracts] :
    (reedyRight Q).IsStableUnderRetracts := by
  rw [reedyRight_eq_matchingClass]
  infer_instance

end Matching

end CategoryTheory.SimplicialObject
