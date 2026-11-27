/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Presentable.Uniformization
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.ObjectProperty.IsClosedUnderCardinalFilteredColimits
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import MathlibExt.CategoryTheory.Comma.IsoComma
public import MathlibExt.CategoryTheory.Presentable.FullSubcategory
public import MathlibExt.CategoryTheory.Presentable.BoundedDiagramClosure

/-!
# The original inverse image and compatible isomorphism-comma presentations

The inverse-image full subcategory is compared with the actual comma objects
whose comparison arrow is invertible. Its original objects, morphisms, and
the two comparison maps are retained. The rank construction enlarges the
native common accessibility rank to include a working-small constraint
family. Filtered-colimit closure is kept distinct from compact generation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uC vC uD vD uE vE uJ vJ uσ

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presentable

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- Compatibility name for the original comma objects with invertible comparisons. -/
abbrev commaIsomorphisms (F : C ⥤ E) (G : D ⥤ E) : ObjectProperty (Comma F G) :=
  isoCommaProperty F G

/-- Compatibility name for the original category of invertible comparisons and their squares. -/
abbrev IsomorphismComma (F : C ⥤ E) (G : D ⥤ E) :=
  IsoComma F G

instance instIsIsoHomObjCommaCommaIsomorphisms
    (F : C ⥤ E) (G : D ⥤ E) (A : IsomorphismComma F G) : IsIso A.obj.hom :=
  isoCommaIsIso F G A

instance (F : C ⥤ E) (G : D ⥤ E) :
    (commaIsomorphisms F G).IsClosedUnderIsomorphisms :=
  isoCommaProperty_isClosedUnderIsomorphisms F G

section OriginalInverseImage

variable (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]

/-- Compatibility name for the classless embedding by identity comparisons. -/
abbrev inverseImageToIsomorphismComma :
    (P.inverseImage F).FullSubcategory ⥤ IsomorphismComma F P.ι :=
  inverseImageToIsoComma F P

/-- Compatibility name for returning the original object along its invertible comparison. -/
abbrev isomorphismCommaToInverseImage :
    IsomorphismComma F P.ι ⥤ (P.inverseImage F).FullSubcategory :=
  isoCommaToInverseImage F P

/-- Compatibility name for the identity unit on the original inverse-image objects. -/
abbrev inverseImageUnit :
    𝟭 (P.inverseImage F).FullSubcategory ≅
      inverseImageToIsomorphismComma F P ⋙ isomorphismCommaToInverseImage F P :=
  inverseImageIsoCommaUnit F P

/-- Compatibility name for the counit given by the original comparison and its inverse. -/
abbrev inverseImageCounit :
    isomorphismCommaToInverseImage F P ⋙ inverseImageToIsomorphismComma F P ≅
      𝟭 (IsomorphismComma F P.ι) :=
  inverseImageIsoCommaCounit F P

/-- Compatibility name for the canonical equivalence with the original inverse image. -/
abbrev inverseImageEquivalence :
    (P.inverseImage F).FullSubcategory ≌ IsomorphismComma F P.ι :=
  inverseImageIsoCommaEquivalence F P

@[simp]
theorem inverseImageEquivalence_obj_left (A : (P.inverseImage F).FullSubcategory) :
    ((inverseImageEquivalence F P).functor.obj A).obj.left = A.obj :=
  inverseImageIsoCommaEquivalence_functor_obj_left F P A

@[simp]
theorem inverseImageEquivalence_map_left {A B : (P.inverseImage F).FullSubcategory}
    (f : A ⟶ B) : ((inverseImageEquivalence F P).functor.map f).hom.left = f.hom :=
  inverseImageIsoCommaEquivalence_functor_map_left F P f

@[simp]
theorem inverseImageEquivalence_inverse_obj (A : IsomorphismComma F P.ι) :
    ((inverseImageEquivalence F P).inverse.obj A).obj = A.obj.left :=
  inverseImageIsoCommaEquivalence_inverse_obj F P A

@[simp]
theorem inverseImageEquivalence_inverse_map {A B : IsomorphismComma F P.ι} (f : A ⟶ B) :
    ((inverseImageEquivalence F P).inverse.map f).hom = f.hom.left :=
  inverseImageIsoCommaEquivalence_inverse_map F P f

/-- The legacy whole-component statement follows from the canonical pointwise API. -/
theorem inverseImageEquivalence_counit_hom_right :
    (fun A : IsomorphismComma F P.ι =>
      ((inverseImageEquivalence F P).counitIso.hom.app A).hom.right.hom) =
      (fun A => A.obj.hom) := by
  funext A
  exact inverseImageIsoCommaEquivalence_counit_hom_right F P A

/-- The legacy inverse-component statement follows from the same original comparison. -/
theorem inverseImageEquivalence_counit_inv_right :
    (fun A : IsomorphismComma F P.ι =>
      ((inverseImageEquivalence F P).counitIso.inv.app A).hom.right.hom) =
      (fun A : IsomorphismComma F P.ι => inv A.obj.hom) := by
  funext A
  exact inverseImageIsoCommaEquivalence_counit_inv_right F P A

/-- Compatibility name for the original source projection of the inverse equivalence. -/
theorem inverseImageEquivalence_inverse_comp_inclusion :
    (inverseImageEquivalence F P).inverse ⋙ (P.inverseImage F).ι =
      (commaIsomorphisms F P.ι).ι ⋙ Comma.fst F P.ι :=
  inverseImageIsoCommaEquivalence_inverse_comp_inclusion F P

end OriginalInverseImage

section Colimits

variable (F : C ⥤ E) (G : D ⥤ E)

/-- The original comparison of a preserved comma colimit is invertible. -/
theorem comma_colimit_isIso {J : Type uJ} [Category.{vJ} J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G]
    (K : J ⥤ Comma F G) [HasColimit K] (hK : ∀ j, IsIso (K.obj j).hom) :
    IsIso (colimit K).hom := by
  exact (MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.isomorphisms E)
    ((K ⋙ Comma.fst F G) ⋙ F) ((K ⋙ Comma.snd F G) ⋙ G)
    (F.mapCocone ((Comma.fst F G).mapCocone (colimit.cocone K)))
    (G.mapCocone ((Comma.snd F G).mapCocone (colimit.cocone K)))
    (isColimitOfPreserves F (isColimitOfPreserves (Comma.fst F G) (colimit.isColimit K)))
    (isColimitOfPreserves G (isColimitOfPreserves (Comma.snd F G) (colimit.isColimit K)))
    (Functor.whiskerLeft K (Comma.natTrans F G)) hK (colimit K).hom
    (fun j => (colimit.ι K j).w))

instance (J : Type uJ) [Category.{vJ} J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    (commaIsomorphisms F G).IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨K, hK⟩
  exact comma_colimit_isIso F G K hK

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
variable [HasCardinalFilteredColimits C κ] [HasCardinalFilteredColimits D κ]
variable [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]

instance : (commaIsomorphisms F G).IsClosedUnderCardinalFilteredColimits κ where
  isCardinalClosedUnderColimitsOfShape' J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have := HasCardinalFilteredColimits.hasColimitsOfShape D κ J
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    have := G.preservesColimitsOfShape_of_isCardinalAccessible κ J
    infer_instance

/-- Actual compact endpoint comparisons are compact in the original isomorphism category. -/
theorem isomorphismComma_presentable (A : IsomorphismComma F G)
    [F.PreservesCardinalPresentable κ]
    [IsCardinalPresentable A.obj.left κ] [IsCardinalPresentable A.obj.right κ] :
    IsCardinalPresentable A κ := by
  have : IsCardinalPresentable A.obj κ := Comma.isCardinalPresentable_mk A.obj.hom
  exact (commaIsomorphisms F G).isCardinalPresentable_of_ι κ A

end Colimits

/-- Enlarge the actual native common strong accessibility rank to bound the constraint labels.
The two original functors and all category carriers remain the supplied ones. -/
theorem exists_inverseImage_comparison_rank
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D] [IsAccessibleCategory.{w} E]
    (F : C ⥤ E) (G : D ⥤ E) [Functor.IsAccessible.{w} F] [Functor.IsAccessible.{w} G]
    (σ : Type uσ) [Small.{w} σ] :
    ∃ (μ κ : Cardinal.{w}) (_ : Fact μ.IsRegular) (_ : Fact κ.IsRegular),
      μ.SharplyLT κ ∧ HasCardinalLT σ κ ∧
        IsCardinalAccessibleCategory C μ ∧ IsCardinalAccessibleCategory D μ ∧
        IsCardinalAccessibleCategory E μ ∧ F.IsCardinalAccessible μ ∧
        G.IsCardinalAccessible μ ∧ F.PreservesCardinalPresentable μ ∧
        G.PreservesCardinalPresentable μ := by
  obtain ⟨μ, hμ, hC, hE, hD, _, hF, hG, hF', hG'⟩ :=
    IsCardinalAccessibleCategory.uniformization_pair F G
  have : Fact μ.IsRegular := hμ
  obtain ⟨κ₀, hκ₀, hσ⟩ := HasCardinalLT.exists_regular_cardinal.{w} σ
  have : Fact κ₀.IsRegular := ⟨hκ₀⟩
  obtain ⟨κ, hκ, hμκ, hκ₀κ⟩ := Cardinal.SharplyLT.exists_of_pair μ κ₀
  exact ⟨μ, κ, hμ, hκ, hμκ, hσ.of_le hκ₀κ.le, hC, hD, hE, hF, hG, hF', hG'⟩

namespace IsomorphismComma

section InverseFactors

variable (μ : Cardinal.{w}) [Fact μ.IsRegular]
variable (F : C ⥤ E) (G : D ⥤ E)
variable [IsCardinalAccessibleCategory C μ] [IsCardinalAccessibleCategory D μ]
variable [F.IsCardinalAccessible μ] [G.IsCardinalAccessible μ]
variable [F.PreservesCardinalPresentable μ] [G.PreservesCardinalPresentable μ]
variable {J : Type w} [PartialOrder J] [IsCardinalFiltered J μ]
variable {A : Comma F G} [IsIso A.hom] (p : ColimitPresentation J A)
variable [∀ j, IsCardinalPresentable (p.diag.obj j).left μ]
variable [∀ j, IsCardinalPresentable (p.diag.obj j).right μ]

private def sourceColimit :
    IsColimit (F.mapCocone ((Comma.fst F G).mapCocone p.cocone)) := by
  have := (Comma.fst F G).preservesColimitsOfShape_of_isCardinalAccessible μ J
  have := F.preservesColimitsOfShape_of_isCardinalAccessible μ J
  exact isColimitOfPreserves F (isColimitOfPreserves (Comma.fst F G) p.isColimit)

private def targetColimit :
    IsColimit (G.mapCocone ((Comma.snd F G).mapCocone p.cocone)) := by
  have := (Comma.snd F G).preservesColimitsOfShape_of_isCardinalAccessible μ J
  have := G.preservesColimitsOfShape_of_isCardinalAccessible μ J
  exact isColimitOfPreserves G (isColimitOfPreserves (Comma.snd F G) p.isColimit)

omit [G.IsCardinalAccessible μ] [F.PreservesCardinalPresentable μ]
  [∀ j, IsCardinalPresentable (p.diag.obj j).left μ] in
include μ in
/-- The same original inverse factors through one of the original source components. -/
private theorem inverse_factor_exists (j : J) :
    ∃ (k : J) (b : G.obj (p.diag.obj j).right ⟶ F.obj (p.diag.obj k).left),
      b ≫ F.map (p.ι.app k).left = G.map (p.ι.app j).right ≫ inv A.hom := by
  exact IsCardinalPresentable.exists_hom_of_isColimit μ (sourceColimit μ F G p)
    (G.map (p.ι.app j).right ≫ inv A.hom)

private def inverseIndex (j : J) : J := (inverse_factor_exists μ F G p j).choose

private def inverseMap (j : J) :
    G.obj (p.diag.obj j).right ⟶ F.obj (p.diag.obj (inverseIndex μ F G p j)).left :=
  (inverse_factor_exists μ F G p j).choose_spec.choose

omit [G.IsCardinalAccessible μ] [F.PreservesCardinalPresentable μ]
  [∀ j, IsCardinalPresentable (p.diag.obj j).left μ] in
private theorem inverseMap_fac (j : J) :
    inverseMap μ F G p j ≫ F.map (p.ι.app (inverseIndex μ F G p j)).left =
      G.map (p.ι.app j).right ≫ inv A.hom :=
  (inverse_factor_exists μ F G p j).choose_spec.choose_spec

omit [IsIso A.hom] in
private theorem source_transition (j k : J) (h : j ≤ k) :
    F.map (p.diag.map (homOfLE h)).left ≫ F.map (p.ι.app k).left =
      F.map (p.ι.app j).left := by
  rw [← F.map_comp]
  congr 1
  exact congrArg CommaMorphism.left (p.w (homOfLE h))

omit [IsIso A.hom] in
private theorem target_transition (j k : J) (h : j ≤ k) :
    G.map (p.diag.map (homOfLE h)).right ≫ G.map (p.ι.app k).right =
      G.map (p.ι.app j).right := by
  rw [← G.map_comp]
  congr 1
  exact congrArg CommaMorphism.right (p.w (homOfLE h))

omit [G.IsCardinalAccessible μ] [F.PreservesCardinalPresentable μ]
  [∀ j, IsCardinalPresentable (p.diag.obj j).left μ] in
/-- Inverse factors agree after an actual original source transition. -/
private theorem inverse_naturality_exists {j j' : J} (h : j ≤ j') :
    ∃ (k : J) (a : inverseIndex μ F G p j ⟶ k)
      (b : inverseIndex μ F G p j' ⟶ k),
      inverseMap μ F G p j ≫ F.map (p.diag.map a).left =
        (G.map (p.diag.map (homOfLE h)).right ≫
          inverseMap μ F G p j') ≫ F.map (p.diag.map b).left := by
  apply IsCardinalPresentable.exists_eq_of_isColimit μ (sourceColimit μ F G p)
  change inverseMap μ F G p j ≫ F.map (p.ι.app (inverseIndex μ F G p j)).left =
    (G.map (p.diag.map (homOfLE h)).right ≫ inverseMap μ F G p j') ≫
      F.map (p.ι.app (inverseIndex μ F G p j')).left
  rw [inverseMap_fac, Category.assoc, inverseMap_fac, ← Category.assoc,
    target_transition]

omit [G.IsCardinalAccessible μ] in
/-- The original left inverse equation holds after an actual source transition. -/
private theorem inverse_left_exists (j : J) :
    ∃ (k : J) (a : inverseIndex μ F G p j ⟶ k) (b : j ⟶ k),
      ((p.diag.obj j).hom ≫ inverseMap μ F G p j) ≫ F.map (p.diag.map a).left =
        F.map (p.diag.map b).left := by
  have heq : ((p.diag.obj j).hom ≫ inverseMap μ F G p j) ≫
      F.map (p.ι.app (inverseIndex μ F G p j)).left =
      (𝟙 (F.obj (p.diag.obj j).left)) ≫ F.map (p.ι.app j).left := by
    rw [Category.id_comp, Category.assoc, inverseMap_fac]
    have hw : F.map (p.ι.app j).left ≫ A.hom =
        (p.diag.obj j).hom ≫ G.map (p.ι.app j).right := (p.ι.app j).w
    calc
      (p.diag.obj j).hom ≫ (G.map (p.ι.app j).right ≫ inv A.hom) =
          F.map (p.ι.app j).left ≫ A.hom ≫ inv A.hom := by
        rw [← Category.assoc, ← hw, Category.assoc]
      _ = F.map (p.ι.app j).left := by simp
  obtain ⟨k, a, b, hab⟩ := IsCardinalPresentable.exists_eq_of_isColimit μ
    (sourceColimit μ F G p) ((p.diag.obj j).hom ≫ inverseMap μ F G p j)
    (𝟙 (F.obj (p.diag.obj j).left)) heq
  exact ⟨k, a, b, by simpa only [Functor.comp_obj, Functor.comp_map,
    Comma.fst_obj, Comma.fst_map, Category.id_comp] using hab⟩

omit [F.PreservesCardinalPresentable μ]
  [∀ j, IsCardinalPresentable (p.diag.obj j).left μ] in
/-- The original right inverse equation holds after an actual target transition. -/
private theorem inverse_right_exists (j : J) :
    ∃ (k : J) (a : inverseIndex μ F G p j ⟶ k) (b : j ⟶ k),
      (inverseMap μ F G p j ≫ (p.diag.obj (inverseIndex μ F G p j)).hom) ≫
        G.map (p.diag.map a).right = G.map (p.diag.map b).right := by
  have heq : (inverseMap μ F G p j ≫ (p.diag.obj (inverseIndex μ F G p j)).hom) ≫
      G.map (p.ι.app (inverseIndex μ F G p j)).right =
      (𝟙 (G.obj (p.diag.obj j).right)) ≫ G.map (p.ι.app j).right := by
    rw [Category.id_comp, Category.assoc]
    have hw : F.map (p.ι.app (inverseIndex μ F G p j)).left ≫ A.hom =
        (p.diag.obj (inverseIndex μ F G p j)).hom ≫
          G.map (p.ι.app (inverseIndex μ F G p j)).right :=
      (p.ι.app (inverseIndex μ F G p j)).w
    calc
      inverseMap μ F G p j ≫ ((p.diag.obj (inverseIndex μ F G p j)).hom ≫
          (G.map (p.ι.app (inverseIndex μ F G p j)).right)) =
          inverseMap μ F G p j ≫ (F.map (p.ι.app (inverseIndex μ F G p j)).left ≫ A.hom) := by
        rw [← hw]
      _ = G.map (p.ι.app j).right ≫ inv A.hom ≫ A.hom := by
        rw [← Category.assoc, inverseMap_fac, Category.assoc]
      _ = G.map (p.ι.app j).right := by simp
  obtain ⟨k, a, b, hab⟩ := IsCardinalPresentable.exists_eq_of_isColimit μ
    (targetColimit μ F G p)
    (inverseMap μ F G p j ≫ (p.diag.obj (inverseIndex μ F G p j)).hom)
    (𝟙 (G.obj (p.diag.obj j).right)) heq
  exact ⟨k, a, b, by simpa only [Functor.comp_obj, Functor.comp_map,
    Comma.snd_obj, Comma.snd_map, Category.id_comp] using hab⟩

private def leftIndex (j : J) : J := (inverse_left_exists μ F G p j).choose

private def leftFromInverse (j : J) : inverseIndex μ F G p j ⟶ leftIndex μ F G p j :=
  (inverse_left_exists μ F G p j).choose_spec.choose

private def leftFromSource (j : J) : j ⟶ leftIndex μ F G p j :=
  (inverse_left_exists μ F G p j).choose_spec.choose_spec.choose

omit [G.IsCardinalAccessible μ] in
private theorem left_equation (j : J) :
    ((p.diag.obj j).hom ≫ inverseMap μ F G p j) ≫
      F.map (p.diag.map (leftFromInverse μ F G p j)).left =
        F.map (p.diag.map (leftFromSource μ F G p j)).left :=
  (inverse_left_exists μ F G p j).choose_spec.choose_spec.choose_spec

private def rightIndex (j : J) : J := (inverse_right_exists μ F G p j).choose

private def rightFromInverse (j : J) : inverseIndex μ F G p j ⟶ rightIndex μ F G p j :=
  (inverse_right_exists μ F G p j).choose_spec.choose

private def rightFromSource (j : J) : j ⟶ rightIndex μ F G p j :=
  (inverse_right_exists μ F G p j).choose_spec.choose_spec.choose

omit [F.PreservesCardinalPresentable μ]
  [∀ j, IsCardinalPresentable (p.diag.obj j).left μ] in
private theorem right_equation (j : J) :
    (inverseMap μ F G p j ≫ (p.diag.obj (inverseIndex μ F G p j)).hom) ≫
      G.map (p.diag.map (rightFromInverse μ F G p j)).right =
        G.map (p.diag.map (rightFromSource μ F G p j)).right :=
  (inverse_right_exists μ F G p j).choose_spec.choose_spec.choose_spec

private def naturalityIndex {j j' : J} (h : j ≤ j') : J :=
  (inverse_naturality_exists μ F G p h).choose

private def naturalityFromFirst {j j' : J} (h : j ≤ j') :
    inverseIndex μ F G p j ⟶ naturalityIndex μ F G p h :=
  (inverse_naturality_exists μ F G p h).choose_spec.choose

private def naturalityFromSecond {j j' : J} (h : j ≤ j') :
    inverseIndex μ F G p j' ⟶ naturalityIndex μ F G p h :=
  (inverse_naturality_exists μ F G p h).choose_spec.choose_spec.choose

omit [G.IsCardinalAccessible μ] [F.PreservesCardinalPresentable μ]
  [∀ j, IsCardinalPresentable (p.diag.obj j).left μ] in
private theorem naturality_equation {j j' : J} (h : j ≤ j') :
    inverseMap μ F G p j ≫ F.map (p.diag.map (naturalityFromFirst μ F G p h)).left =
      (G.map (p.diag.map (homOfLE h)).right ≫ inverseMap μ F G p j') ≫
        F.map (p.diag.map (naturalityFromSecond μ F G p h)).left :=
  (inverse_naturality_exists μ F G p h).choose_spec.choose_spec.choose_spec

/-- All four compatibility requirements are obtained from the actual original inverse. -/
private def constraints (s : Fin 4) (xs : List J) : J := by
  classical
  have : Nonempty J := (isFiltered_of_isCardinalFiltered J μ).nonempty
  exact match s.val, xs with
    | 0, [j] => inverseIndex μ F G p j
    | 1, [j] => leftIndex μ F G p j
    | 2, [j] => rightIndex μ F G p j
    | 3, [j, j'] => if h : j ≤ j' then naturalityIndex μ F G p h else j
    | _, _ => Classical.arbitrary J

private theorem closed_inverse (B : Set J)
    (hB : ∀ (s : Fin 4) (xs : List B),
      constraints μ F G p s (xs.map Subtype.val) ∈ B) {j : J} (hj : j ∈ B) :
    inverseIndex μ F G p j ∈ B := by
  simpa [constraints] using hB 0 [⟨j, hj⟩]

private theorem closed_left (B : Set J)
    (hB : ∀ (s : Fin 4) (xs : List B),
      constraints μ F G p s (xs.map Subtype.val) ∈ B) {j : J} (hj : j ∈ B) :
    leftIndex μ F G p j ∈ B := by
  simpa [constraints] using hB 1 [⟨j, hj⟩]

private theorem closed_right (B : Set J)
    (hB : ∀ (s : Fin 4) (xs : List B),
      constraints μ F G p s (xs.map Subtype.val) ∈ B) {j : J} (hj : j ∈ B) :
    rightIndex μ F G p j ∈ B := by
  simpa [constraints] using hB 2 [⟨j, hj⟩]

private theorem closed_naturality (B : Set J)
    (hB : ∀ (s : Fin 4) (xs : List B),
      constraints μ F G p s (xs.map Subtype.val) ∈ B)
    {j j' : J} (hj : j ∈ B) (hj' : j' ∈ B) (h : j ≤ j') :
    naturalityIndex μ F G p h ∈ B := by
  simpa [constraints, h] using hB 3 [⟨j, hj⟩, ⟨j', hj'⟩]

/-- Reuse the exact original diagram and legs as a native compact comma presentation. -/
private def compactPresentation :
    (isCardinalPresentable (Comma F G) μ).ColimitOfShape J A where
  diag := p.diag
  ι := p.ι
  isColimit := p.isColimit
  prop_diag_obj j := by
    change IsCardinalPresentable (p.diag.obj j) μ
    exact Comma.isCardinalPresentable_mk (p.diag.obj j).hom

variable [LocallySmall.{w} E]
variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

private abbrev pieceDiagram
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J)) :
    B.val ⥤ Comma F G :=
  B.val.mono_coe.functor ⋙ (compactPresentation μ F G p).diag

private abbrev piece
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J)) : Comma F G :=
  Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.colimit μ κ
    (compactPresentation μ F G p) B

/-- The actual native restriction leg with its original source object stated explicitly. -/
private def pieceLeg
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J))
    (j : J) (hj : j ∈ B.val) : p.diag.obj j ⟶ piece μ F G p κ B := by
  exact colimit.ι (pieceDiagram μ F G p κ B) ⟨j, hj⟩

private def pieceSourceColimit
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J)) :
    IsColimit (F.mapCocone ((Comma.fst F G).mapCocone
      (colimit.cocone (pieceDiagram μ F G p κ B)))) := by
  have : IsCardinalFiltered B.val μ := B.property.1
  have := (Comma.fst F G).preservesColimitsOfShape_of_isCardinalAccessible μ B.val
  have := F.preservesColimitsOfShape_of_isCardinalAccessible μ B.val
  exact isColimitOfPreserves F
    (isColimitOfPreserves (Comma.fst F G) (colimit.isColimit _))

private def pieceTargetColimit
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J)) :
    IsColimit (G.mapCocone ((Comma.snd F G).mapCocone
      (colimit.cocone (pieceDiagram μ F G p κ B)))) := by
  have : IsCardinalFiltered B.val μ := B.property.1
  have := (Comma.snd F G).preservesColimitsOfShape_of_isCardinalAccessible μ B.val
  have := G.preservesColimitsOfShape_of_isCardinalAccessible μ B.val
  exact isColimitOfPreserves G
    (isColimitOfPreserves (Comma.snd F G) (colimit.isColimit _))

omit [G.PreservesCardinalPresentable μ] [IsCardinalFiltered J μ]
  [IsIso A.hom] [Fact κ.IsRegular] in
private theorem piece_source_transition
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J))
    {j k : J} (hj : j ∈ B.val) (hk : k ∈ B.val) (a : j ⟶ k) :
    F.map (p.diag.map a).left ≫
      F.map ((pieceLeg μ F G p κ B (k) (hk))).left =
        F.map ((pieceLeg μ F G p κ B (j) (hj))).left := by
  let aB : (⟨j, hj⟩ : B.val) ⟶ ⟨k, hk⟩ := homOfLE (leOfHom a)
  have ha : B.val.mono_coe.functor.map aB = a := Subsingleton.elim _ _
  have hw := congrArg CommaMorphism.left (colimit.w (pieceDiagram μ F G p κ B) aB)
  rw [← F.map_comp]
  congr 1

omit [G.PreservesCardinalPresentable μ] [IsCardinalFiltered J μ]
  [IsIso A.hom] [Fact κ.IsRegular] in
private theorem piece_target_transition
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J))
    {j k : J} (hj : j ∈ B.val) (hk : k ∈ B.val) (a : j ⟶ k) :
    G.map (p.diag.map a).right ≫
      G.map ((pieceLeg μ F G p κ B (k) (hk))).right =
        G.map ((pieceLeg μ F G p κ B (j) (hj))).right := by
  let aB : (⟨j, hj⟩ : B.val) ⟶ ⟨k, hk⟩ := homOfLE (leOfHom a)
  have ha : B.val.mono_coe.functor.map aB = a := Subsingleton.elim _ _
  have hw := congrArg CommaMorphism.right (colimit.w (pieceDiagram μ F G p κ B) aB)
  rw [← G.map_comp]
  congr 1

/-- The original inverse factors descend along every actual compatible bounded restriction. -/
private def inverseCocone
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J))
    (hB : ∀ (s : Fin 4) (xs : List B.val),
      constraints μ F G p s (xs.map Subtype.val) ∈ B.val) :
    Cocone ((pieceDiagram μ F G p κ B ⋙ Comma.snd F G) ⋙ G) where
  pt := F.obj (piece μ F G p κ B).left
  ι.app j := inverseMap μ F G p j.val ≫
    F.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j.val)
      (closed_inverse μ F G p B.val hB j.property)).left
  ι.naturality j j' f := by
    let h : j.val ≤ j'.val := leOfHom f
    have hk := closed_naturality μ F G p B.val hB j.property j'.property h
    have h₁ := piece_source_transition μ F G p κ B
      (closed_inverse μ F G p B.val hB j.property) hk (naturalityFromFirst μ F G p h)
    have h₂ := piece_source_transition μ F G p κ B
      (closed_inverse μ F G p B.val hB j'.property) hk (naturalityFromSecond μ F G p h)
    have hf : B.val.mono_coe.functor.map f = homOfLE h := Subsingleton.elim _ _
    change G.map (p.diag.map (B.val.mono_coe.functor.map f)).right ≫
        (inverseMap μ F G p j'.val ≫
          F.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j'.val) _).left) =
      (inverseMap μ F G p j.val ≫
        F.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j.val) _).left) ≫ 𝟙 _
    rw [hf, Category.comp_id]
    calc
      G.map (p.diag.map (homOfLE h)).right ≫
          (inverseMap μ F G p j'.val ≫
            F.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j'.val) _).left) =
          ((G.map (p.diag.map (homOfLE h)).right ≫ inverseMap μ F G p j'.val) ≫
            F.map (p.diag.map (naturalityFromSecond μ F G p h)).left) ≫
              F.map (pieceLeg μ F G p κ B (naturalityIndex μ F G p h) hk).left := by
        simp only [Category.assoc, h₂]
      _ = (inverseMap μ F G p j.val ≫
          F.map (p.diag.map (naturalityFromFirst μ F G p h)).left) ≫
            F.map (pieceLeg μ F G p κ B (naturalityIndex μ F G p h) hk).left := by
        rw [← naturality_equation μ F G p h]
      _ = inverseMap μ F G p j.val ≫
          F.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j.val) _).left := by
        simp only [Category.assoc, h₁]

private def pieceInverse
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J))
    (hB : ∀ (s : Fin 4) (xs : List B.val),
      constraints μ F G p s (xs.map Subtype.val) ∈ B.val) :
    G.obj (piece μ F G p κ B).right ⟶ F.obj (piece μ F G p κ B).left :=
  (pieceTargetColimit μ F G p κ B).desc (inverseCocone μ F G p κ B hB)

omit [Fact κ.IsRegular] in
private theorem pieceInverse_fac
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J))
    (hB : ∀ (s : Fin 4) (xs : List B.val),
      constraints μ F G p s (xs.map Subtype.val) ∈ B.val) (j : J) (hj : j ∈ B.val) :
    G.map (pieceLeg μ F G p κ B j hj).right ≫
      pieceInverse μ F G p κ B hB =
        inverseMap μ F G p j ≫ F.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j)
          (closed_inverse μ F G p B.val hB hj)).left :=
  (pieceTargetColimit μ F G p κ B).fac (inverseCocone μ F G p κ B hB) ⟨j, hj⟩

omit [Fact κ.IsRegular] in
/-- Both original inverse laws hold on the actual colimit of a compatible restriction. -/
private theorem piece_isIso
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J))
    (hB : ∀ (s : Fin 4) (xs : List B.val),
      constraints μ F G p s (xs.map Subtype.val) ∈ B.val) :
    IsIso (piece μ F G p κ B).hom := by
  have hLeft : (piece μ F G p κ B).hom ≫ pieceInverse μ F G p κ B hB = 𝟙 _ := by
    apply (pieceSourceColimit μ F G p κ B).hom_ext
    intro j
    have hjInv := closed_inverse μ F G p B.val hB j.property
    have hjLeft := closed_left μ F G p B.val hB j.property
    have ht₁ := piece_source_transition μ F G p κ B hjInv hjLeft
      (leftFromInverse μ F G p j.val)
    have ht₂ := piece_source_transition μ F G p κ B j.property hjLeft
      (leftFromSource μ F G p j.val)
    change F.map (pieceLeg μ F G p κ B j.val j.property).left ≫
        ((piece μ F G p κ B).hom ≫ pieceInverse μ F G p κ B hB) =
      F.map (pieceLeg μ F G p κ B j.val j.property).left ≫ 𝟙 _
    rw [← Category.assoc, (pieceLeg μ F G p κ B j.val j.property).w,
      Category.assoc, pieceInverse_fac, Category.comp_id]
    calc
      (p.diag.obj j.val).hom ≫ (inverseMap μ F G p j.val ≫
          F.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j.val) hjInv).left) =
          (((p.diag.obj j.val).hom ≫ inverseMap μ F G p j.val) ≫
            F.map (p.diag.map (leftFromInverse μ F G p j.val)).left) ≫
              F.map (pieceLeg μ F G p κ B (leftIndex μ F G p j.val) hjLeft).left := by
        simp only [Category.assoc, ht₁]
      _ = F.map (p.diag.map (leftFromSource μ F G p j.val)).left ≫
          F.map (pieceLeg μ F G p κ B (leftIndex μ F G p j.val) hjLeft).left := by
        rw [left_equation μ F G p j.val]
      _ = F.map (pieceLeg μ F G p κ B j.val j.property).left := ht₂
  have hRight : pieceInverse μ F G p κ B hB ≫ (piece μ F G p κ B).hom = 𝟙 _ := by
    apply (pieceTargetColimit μ F G p κ B).hom_ext
    intro j
    have hjInv := closed_inverse μ F G p B.val hB j.property
    have hjRight := closed_right μ F G p B.val hB j.property
    have ht₁ := piece_target_transition μ F G p κ B hjInv hjRight
      (rightFromInverse μ F G p j.val)
    have ht₂ := piece_target_transition μ F G p κ B j.property hjRight
      (rightFromSource μ F G p j.val)
    change G.map (pieceLeg μ F G p κ B j.val j.property).right ≫
        (pieceInverse μ F G p κ B hB ≫ (piece μ F G p κ B).hom) =
      G.map (pieceLeg μ F G p κ B j.val j.property).right ≫ 𝟙 _
    rw [← Category.assoc, pieceInverse_fac, Category.assoc,
      (pieceLeg μ F G p κ B (inverseIndex μ F G p j.val) hjInv).w, Category.comp_id]
    calc
      inverseMap μ F G p j.val ≫ ((p.diag.obj (inverseIndex μ F G p j.val)).hom ≫
          G.map (pieceLeg μ F G p κ B (inverseIndex μ F G p j.val) hjInv).right) =
          ((inverseMap μ F G p j.val ≫ (p.diag.obj (inverseIndex μ F G p j.val)).hom) ≫
            G.map (p.diag.map (rightFromInverse μ F G p j.val)).right) ≫
              G.map (pieceLeg μ F G p κ B (rightIndex μ F G p j.val) hjRight).right := by
        simp only [Category.assoc, ht₁]
      _ = G.map (p.diag.map (rightFromSource μ F G p j.val)).right ≫
          G.map (pieceLeg μ F G p κ B (rightIndex μ F G p j.val) hjRight).right := by
        rw [right_equation μ F G p j.val]
      _ = G.map (pieceLeg μ F G p κ B j.val j.property).right := ht₂
  exact ⟨pieceInverse μ F G p κ B hB, hLeft, hRight⟩

variable (h : μ.SharplyLT κ)

include h in
/-- Produce an actual bounded restriction with invertible comparison, from any bounded indices. -/
private theorem exists_good_subset (S : Set J) (hS : HasCardinalLT S κ) :
    ∃ (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J)),
      S ⊆ B.val ∧ IsIso (piece μ F G p κ B).hom := by
  obtain ⟨T, hST, hFiltered, hSmall, hClosed⟩ :=
    BoundedDiagramClosure.exists_closed_bounded_filtered_set h (constraints μ F G p)
      (hasCardinalLT_of_finite (Fin 4) κ (Cardinal.IsRegular.aleph0_le Fact.out)) S hS
  let B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J) :=
    ⟨T, hFiltered, hSmall⟩
  exact ⟨B, hST, piece_isIso μ F G p κ B hClosed⟩

/-- Exactly the native bounded indices whose actual colimit comparison is invertible. -/
private def goodSets :
    Set (Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J)) :=
  {B | IsIso (piece μ F G p κ B).hom}

include h in
private theorem goodSets_filtered : IsCardinalFiltered (goodSets μ F G p κ) κ := by
  apply isCardinalFiltered_preorder
  intro T f hT
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hT
  obtain ⟨B, hB, hIso⟩ := exists_good_subset μ F G p κ h (⋃ t, (f t).val.val)
    (hasCardinalLT_iUnion _ hT (fun t => (f t).val.property.2))
  exact ⟨⟨B, hIso⟩, fun t => (Set.subset_iUnion _ t).trans hB⟩

include h in
private theorem goodSets_final : (goodSets μ F G p κ).mono_coe.functor.Final := by
  have : IsCardinalFiltered (goodSets μ F G p κ) κ := goodSets_filtered μ F G p κ h
  have := isFiltered_of_isCardinalFiltered (goodSets μ F G p κ) κ
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · intro B
    obtain ⟨B', hBB', hIso⟩ := exists_good_subset μ F G p κ h B.val B.property.2
    exact ⟨⟨B', hIso⟩, ⟨homOfLE hBB'⟩⟩
  · intro B T s s'
    exact ⟨T, 𝟙 _, Subsingleton.elim _ _⟩

/-- The actual colimits of good restrictions, with the original comparisons and square maps. -/
private def goodDiagram : (goodSets μ F G p κ) ⥤ IsomorphismComma F G :=
  (commaIsomorphisms F G).lift
    ((goodSets μ F G p κ).mono_coe.functor ⋙
      Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.functor μ κ
        (compactPresentation μ F G p)) (fun B => B.property)

/-- The native restriction legs form a cocone with the original comparison as its point. -/
private def goodCocone : Cocone (goodDiagram μ F G p κ) where
  pt := ⟨A, (inferInstance : IsIso A.hom)⟩
  ι.app B := ObjectProperty.homMk
    (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.colimit.π μ κ
      (compactPresentation μ F G p) B.val)
  ι.naturality B B' f := by
    apply ObjectProperty.hom_ext
    change Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.colimit.map μ κ
        (compactPresentation μ F G p) (leOfHom f) ≫
        Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.colimit.π μ κ
          (compactPresentation μ F G p) B'.val =
      Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.colimit.π μ κ
        (compactPresentation μ F G p) B.val ≫ 𝟙 A
    rw [Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.colimit.map_π,
      Category.comp_id]

include h in
/-- The good restrictions really present the original object, by native cofinal colimit reuse. -/
private def goodCocone_isColimit : IsColimit (goodCocone μ F G p κ) := by
  have : (goodSets μ F G p κ).mono_coe.functor.Final := goodSets_final μ F G p κ h
  have hc : IsColimit ((commaIsomorphisms F G).ι.mapCocone (goodCocone μ F G p κ)) := by
    change IsColimit
      ((Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.cocone μ κ
        (compactPresentation μ F G p)).whisker (goodSets μ F G p κ).mono_coe.functor)
    exact (Functor.Final.isColimitWhiskerEquiv (goodSets μ F G p κ).mono_coe.functor _).symm
      (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.isColimit μ κ
        (compactPresentation μ F G p))
  exact isColimitOfReflects (commaIsomorphisms F G).ι hc

omit [G.PreservesCardinalPresentable μ] [IsCardinalFiltered J μ] [IsIso A.hom] in
include h in
/-- Every produced piece is compact at the larger actual regular rank. -/
private theorem piece_presentable
    (B : Subtype (Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT μ κ J)) :
    IsCardinalPresentable (piece μ F G p κ B) κ := by
  have (j : B.val) : IsCardinalPresentable ((pieceDiagram μ F G p κ B).obj j) μ := by
    change IsCardinalPresentable (p.diag.obj j.val) μ
    exact Comma.isCardinalPresentable_mk (p.diag.obj j.val).hom
  have (j : B.val) : IsCardinalPresentable ((pieceDiagram μ F G p κ B).obj j) κ :=
    isCardinalPresentable_of_le _ h.le
  exact isCardinalPresentable_of_isColimit _ (colimit.isColimit (pieceDiagram μ F G p κ B)) κ
    ((hasCardinalLT_arrow_iff_of_isThin B.val κ
      (Cardinal.IsRegular.aleph0_le Fact.out)).mpr B.property.2)

end InverseFactors

section AccessibleCategory

variable (μ κ : Cardinal.{w}) [Fact μ.IsRegular] [Fact κ.IsRegular]
variable (F : C ⥤ E) (G : D ⥤ E)
variable [IsCardinalAccessibleCategory C μ] [IsCardinalAccessibleCategory D μ]
variable [LocallySmall.{w} E]
variable [F.IsCardinalAccessible μ] [G.IsCardinalAccessible μ]
variable [F.PreservesCardinalPresentable μ] [G.PreservesCardinalPresentable μ]

/-- The original isomorphism-comma category is accessible at a sharply larger regular rank.
Its compact generating presentations are constructed from the original comparisons. -/
theorem accessible_of_sharplyLT (h : μ.SharplyLT κ) :
    IsCardinalAccessibleCategory (IsomorphismComma F G) κ ∧
      (commaIsomorphisms F G).ι.IsCardinalAccessible κ := by
  have : IsCardinalAccessibleCategory C κ := h.isCardinalAccessibleCategory C
  have : IsCardinalAccessibleCategory D κ := h.isCardinalAccessibleCategory D
  have : F.IsCardinalAccessible κ := Functor.isCardinalAccessible_of_le F h.le
  have : G.IsCardinalAccessible κ := Functor.isCardinalAccessible_of_le G h.le
  have : IsCardinalAccessibleCategory (Comma F G) κ :=
    h.isCardinalAccessibleCategory (Comma F G)
  have : (commaIsomorphisms F G).ι.IsCardinalAccessible κ := inferInstance
  let Q : ObjectProperty (IsomorphismComma F G) :=
    (isCardinalPresentable (Comma F G) κ).inverseImage (commaIsomorphisms F G).ι
  have hQCompact : Q ≤ isCardinalPresentable (IsomorphismComma F G) κ := by
    intro A hA
    have : IsCardinalPresentable A.obj κ := hA
    exact (commaIsomorphisms F G).isCardinalPresentable_of_ι κ A
  have hQSmall : ObjectProperty.EssentiallySmall.{w} Q := by
    let inclusion : Q.FullSubcategory ⥤
        (isCardinalPresentable (Comma F G) κ).FullSubcategory :=
      (isCardinalPresentable (Comma F G) κ).lift
        (Q.ι ⋙ (commaIsomorphisms F G).ι) (fun A => A.property)
    have : inclusion.Full := {
      map_surjective f := ⟨ObjectProperty.homMk (ObjectProperty.homMk f.hom), rfl⟩ }
    have : inclusion.Faithful := by
      constructor
      intro A B f g hfg
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact congrArg (fun t => t.hom) hfg
    have : EssentiallySmall.{w} Q.FullSubcategory :=
      essentiallySmall_of_fully_faithful inclusion
    apply (ObjectProperty.exists_equivalence_iff Q).mp
    exact ⟨SmallModel.{w} Q.FullSubcategory, inferInstance,
      ⟨equivSmallModel.{w} Q.FullSubcategory⟩⟩
  have hQGenerator : Q.IsCardinalFilteredGenerator κ := by
    refine ⟨hQCompact, ?_⟩
    intro X
    have : IsIso X.obj.hom := X.property
    have hGenerator := isCardinalFilteredGenerator_isCardinalPresentable (Comma F G) μ
    obtain ⟨J₀, _, _, ⟨p₀⟩⟩ := hGenerator.exists_colimitsOfShape X.obj
    obtain ⟨J, _, _, K, _⟩ := IsCardinalFiltered.exists_cardinal_directed J₀ μ
    let p := p₀.reindex K
    have (j : J) : IsCardinalPresentable (p.diag.obj j) μ := p.prop_diag_obj j
    have (j : J) : IsCardinalPresentable (p.diag.obj j).left μ :=
      inferInstanceAs (IsCardinalPresentable ((Comma.fst F G).obj (p.diag.obj j)) μ)
    have (j : J) : IsCardinalPresentable (p.diag.obj j).right μ :=
      inferInstanceAs (IsCardinalPresentable ((Comma.snd F G).obj (p.diag.obj j)) μ)
    let pres := p.toColimitPresentation
    refine ⟨goodSets μ F G pres κ, inferInstance,
      goodSets_filtered μ F G pres κ h, ⟨?_⟩⟩
    exact {
      diag := goodDiagram μ F G pres κ
      ι := (goodCocone μ F G pres κ).ι
      isColimit := goodCocone_isColimit μ F G pres κ h
      prop_diag_obj j := piece_presentable μ F G pres κ h j.val }
  have : HasCardinalFilteredGenerator (IsomorphismComma F G) κ :=
    ⟨Q, hQSmall, hQGenerator⟩
  exact ⟨{ toHasCardinalFilteredGenerator := inferInstance }, inferInstance⟩

end AccessibleCategory

end IsomorphismComma

/-- Accessibility of the original inverse image, with a genuinely produced common regular rank.
The category and its original inclusion are both proved accessible; their objects and arrows
are the original ones. The accessible full class and inclusion are the stated mathematical
inputs, not a supplied presentation of the desired inverse image. -/
theorem inverseImage_accessible
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    (F : C ⥤ D) [Functor.IsAccessible.{w} F]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [IsAccessibleCategory.{w} P.FullSubcategory] [Functor.IsAccessible.{w} P.ι] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (P.inverseImage F).FullSubcategory κ ∧
        (P.inverseImage F).ι.IsCardinalAccessible κ := by
  obtain ⟨μ, κ, hμ, hκ, hSharp, _, hC, hP, hD, hF, hι, hF', hι'⟩ :=
    exists_inverseImage_comparison_rank F P.ι (Fin 4)
  have : Fact μ.IsRegular := hμ
  have : Fact κ.IsRegular := hκ
  have : IsCardinalAccessibleCategory C μ := hC
  have : IsCardinalAccessibleCategory P.FullSubcategory μ := hP
  have : IsCardinalAccessibleCategory D μ := hD
  have : F.IsCardinalAccessible μ := hF
  have : P.ι.IsCardinalAccessible μ := hι
  have : F.PreservesCardinalPresentable μ := hF'
  have : P.ι.PreservesCardinalPresentable μ := hι'
  obtain ⟨hIso, hInclusion⟩ := IsomorphismComma.accessible_of_sharplyLT μ κ F P.ι hSharp
  have : IsCardinalAccessibleCategory (IsomorphismComma F P.ι) κ := hIso
  have : (commaIsomorphisms F P.ι).ι.IsCardinalAccessible κ := hInclusion
  have : IsCardinalAccessibleCategory C κ := hSharp.isCardinalAccessibleCategory C
  have : IsCardinalAccessibleCategory P.FullSubcategory κ :=
    hSharp.isCardinalAccessibleCategory P.FullSubcategory
  have : F.IsCardinalAccessible κ := Functor.isCardinalAccessible_of_le F hSharp.le
  let e := inverseImageEquivalence F P
  have hOriginal : IsCardinalAccessibleCategory (P.inverseImage F).FullSubcategory κ :=
    e.symm.isCardinalAccessibleCategory κ
  have hProjection :
      ((commaIsomorphisms F P.ι).ι ⋙ Comma.fst F P.ι).IsCardinalAccessible κ := inferInstance
  have : (e.inverse ⋙ (P.inverseImage F).ι).IsCardinalAccessible κ := by
    simpa only [e, inverseImageEquivalence_inverse_comp_inclusion] using hProjection
  have : e.functor.IsCardinalAccessible κ := inferInstance
  let comparison : (e.functor ⋙ (e.inverse ⋙ (P.inverseImage F).ι)) ≅ (P.inverseImage F).ι :=
    (Functor.associator e.functor e.inverse (P.inverseImage F).ι).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm (P.inverseImage F).ι ≪≫
        (P.inverseImage F).ι.leftUnitor
  exact ⟨κ, hκ, hOriginal, Functor.isCardinalAccessible_of_natIso comparison κ⟩

end CategoryTheory.Presentable
