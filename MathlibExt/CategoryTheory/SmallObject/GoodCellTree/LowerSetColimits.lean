/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Order.UpperLower.Closure

/-!
# Actual colimits on lower subsets of a preorder

The maps in this file are defined from chosen cocones. Their vertex equations,
identity/composition laws, lower-union pushout and filtered-union colimit
retain those same choices. The coefficient category is arbitrary.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w v u vI uI

namespace CategoryTheory.SmallObject

open CategoryTheory.Limits

namespace LowerSetColimits

variable {P : Type w} [Preorder P] {C : Type u} [Category.{v} C]

/-- The actual inclusion of the subtype of a set into the original preorder. -/
abbrev inclusion (B : Set P) : B ⥤ P where
  obj a := a.1
  map f := homOfLE (leOfHom f)

/-- The original diagram restricted to a lower label set. -/
abbrev restriction (Y : P ⥤ C) (B : LowerSet P) : B ⥤ C :=
  inclusion (B : Set P) ⋙ Y

/-- Convert the exact lower-order proof to its original carrier subset function. -/
abbrev memOfLE {B D : LowerSet P} (h : B ≤ D) {a : P} (ha : a ∈ B) : a ∈ D :=
  (LowerSet.coe_subset_coe.2 h) ha

/-- A label inclusion, keeping the original underlying elements. -/
abbrev lowerInclusion {B D : LowerSet P} (h : B ≤ D) : B ⥤ D where
  obj a := ⟨a.1, memOfLE h a.2⟩
  map f := homOfLE (leOfHom f)

@[simp]
theorem inclusion_obj (B : Set P) (a : B) : (inclusion B).obj a = a.1 := rfl

@[simp]
theorem restriction_obj (Y : P ⥤ C) (B : LowerSet P) (a : B) :
    (restriction Y B).obj a = Y.obj a.1 := rfl

@[simp]
theorem restriction_map (Y : P ⥤ C) (B : LowerSet P) {a b : B} (f : a ⟶ b) :
    (restriction Y B).map f = Y.map (homOfLE (leOfHom f)) := rfl

end LowerSetColimits

/-- Chosen actual colimit cocones for all lower restrictions of one original diagram. -/
structure LowerSetColimitData {P : Type w} [Preorder P]
    {C : Type u} [Category.{v} C] (Y : P ⥤ C) where
  /-- The cocone over each original lower restriction. -/
  cocone (B : LowerSet P) : Cocone (LowerSetColimits.restriction Y B)
  /-- Its actual colimit universal property. -/
  isColimit (B : LowerSet P) : IsColimit (cocone B)

namespace LowerSetColimitData

open LowerSetColimits

variable {P : Type w} [Preorder P] {C : Type u} [Category.{v} C]
  {Y : P ⥤ C} (L : LowerSetColimitData Y)

/-- The actual selected lower-piece object. -/
abbrev obj (B : LowerSet P) : C := (L.cocone B).pt

/-- The original vertex leg into its selected lower piece. -/
abbrev ι (B : LowerSet P) (a : B) : Y.obj a.1 ⟶ L.obj B :=
  (L.cocone B).ι.app a

/-- Restrict the larger selected cocone along an actual inclusion of labels. -/
abbrev restrictedCocone {B D : LowerSet P} (h : B ≤ D) :
    Cocone (restriction Y B) where
  pt := L.obj D
  ι :=
    { app a := L.ι D ⟨a.1, memOfLE h a.2⟩
      naturality a b f := by
        change Y.map (homOfLE (leOfHom f)) ≫ L.ι D ⟨b.1, memOfLE h b.2⟩ =
          L.ι D ⟨a.1, memOfLE h a.2⟩ ≫ 𝟙 _
        simpa only [restriction, inclusion, Functor.comp_map, ι, Category.comp_id] using
          (L.cocone D).w
            (homOfLE (leOfHom f) :
              (⟨a.1, memOfLE h a.2⟩ : D) ⟶ (⟨b.1, memOfLE h b.2⟩ : D)) }

/-- The unique comparison preserving every original vertex leg. -/
abbrev map {B D : LowerSet P} (h : B ≤ D) : L.obj B ⟶ L.obj D :=
  (L.isColimit B).desc (L.restrictedCocone h)

@[reassoc]
theorem ι_map {B D : LowerSet P} (h : B ≤ D) (a : B) :
    L.ι B a ≫ L.map h = L.ι D ⟨a.1, memOfLE h a.2⟩ :=
  (L.isColimit B).fac (L.restrictedCocone h) a

@[reassoc]
theorem map_id (B : LowerSet P) : L.map (le_refl B) = 𝟙 (L.obj B) := by
  apply (L.isColimit B).hom_ext
  intro a
  simp only [ι_map, Category.comp_id]

@[reassoc]
theorem map_comp {B D E : LowerSet P} (hBD : B ≤ D) (hDE : D ≤ E) :
    L.map hBD ≫ L.map hDE = L.map (hBD.trans hDE) := by
  apply (L.isColimit B).hom_ext
  intro a
  change L.ι B a ≫ (L.map hBD ≫ L.map hDE) = L.ι B a ≫ L.map (hBD.trans hDE)
  rw [L.ι_map_assoc hBD a, L.ι_map hDE, L.ι_map (hBD.trans hDE)]

/-- All selected pieces and their actual comparison functions form a functor. -/
abbrev functor : LowerSet P ⥤ C where
  obj B := L.obj B
  map h := L.map (leOfHom h)
  map_id B := L.map_id B
  map_comp f g := (L.map_comp (leOfHom f) (leOfHom g)).symm

/-- Choose lower-piece cocones from the existing working-size colimits. -/
def ofHasColimits (Y : P ⥤ C) [HasColimitsOfSize.{w, w} C] :
    LowerSetColimitData Y where
  cocone B := colimit.cocone (restriction Y B)
  isColimit B := colimit.isColimit (restriction Y B)

/-- The lower-piece vertex legs detect equality of actual maps. -/
theorem hom_ext {B : LowerSet P} {Z : C} {f g : L.obj B ⟶ Z}
    (h : ∀ a : B, L.ι B a ≫ f = L.ι B a ≫ g) : f = g :=
  (L.isColimit B).hom_ext h

/-- An actual cocone on the empty lower restriction. -/
abbrev emptyCocone (Z : C) : Cocone (restriction Y (⊥ : LowerSet P)) where
  pt := Z
  ι :=
    { app a := False.elim (LowerSet.notMem_bot a.2)
      naturality a _ _ := False.elim (LowerSet.notMem_bot a.2) }

/-- The selected empty lower piece is initial in the coefficient category. -/
def isInitialObjBot : IsInitial (L.obj (⊥ : LowerSet P)) :=
  IsInitial.ofUniqueHom
    (fun Z => (L.isColimit ⊥).desc (emptyCocone (Y := Y) Z))
    (fun _ _ => L.hom_ext (fun a => False.elim (LowerSet.notMem_bot a.2)))

/-- The principal lower cocone keeps the original arrows to its greatest vertex. -/
abbrev principalCocone (a : P) : Cocone (restriction Y (LowerSet.Iic a)) where
  pt := Y.obj a
  ι :=
    { app b := Y.map (homOfLE b.2)
      naturality b c f := by
        change Y.map (homOfLE (leOfHom f)) ≫ Y.map (homOfLE c.2) =
          Y.map (homOfLE b.2) ≫ 𝟙 _
        rw [Category.comp_id, ← Y.map_comp]
        rfl }

/-- The selected principal piece identifies with the original vertex, with actual legs. -/
def principalIso (a : P) : L.obj (LowerSet.Iic a) ≅ Y.obj a where
  hom := (L.isColimit (LowerSet.Iic a)).desc (principalCocone (Y := Y) a)
  inv := L.ι (LowerSet.Iic a) ⟨a, le_rfl⟩
  hom_inv_id := by
    apply L.hom_ext
    intro b
    rw [← Category.assoc, (L.isColimit (LowerSet.Iic a)).fac, Category.comp_id]
    exact (L.cocone (LowerSet.Iic a)).w
      (homOfLE b.2 : b ⟶ (⟨a, le_rfl⟩ : LowerSet.Iic a))
  inv_hom_id := by
    have hh := (L.isColimit (LowerSet.Iic a)).fac
      (principalCocone (Y := Y) a) ⟨a, le_rfl⟩
    change L.ι (LowerSet.Iic a) ⟨a, le_rfl⟩ ≫
      (L.isColimit (LowerSet.Iic a)).desc (principalCocone (Y := Y) a) = Y.map (𝟙 a) at hh
    rw [Y.map_id] at hh
    exact hh

@[reassoc]
theorem ι_principalIso_hom (a : P) (b : LowerSet.Iic a) :
    L.ι (LowerSet.Iic a) b ≫ (L.principalIso a).hom =
      Y.map (homOfLE b.2) :=
  (L.isColimit (LowerSet.Iic a)).fac (principalCocone (Y := Y) a) b

/-- The full lower cocone viewed on the ORIGINAL vertex carrier. -/
abbrev fullCocone : Cocone Y where
  pt := L.obj ⊤
  ι :=
    { app a := L.ι ⊤ ⟨a, by simp⟩
      naturality a b f := by
        change Y.map f ≫ L.ι ⊤ ⟨b, by simp⟩ =
          L.ι ⊤ ⟨a, by simp⟩ ≫ 𝟙 _
        have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
        rw [hf, Category.comp_id]
        exact (L.cocone ⊤).w
          (homOfLE (leOfHom f) :
            (⟨a, by simp⟩ : (⊤ : LowerSet P)) ⟶ (⟨b, by simp⟩ : (⊤ : LowerSet P))) }

/-- Its chosen lower-colimit witness is a whole colimit on the original carrier. -/
def isColimitFullCocone : IsColimit L.fullCocone where
  desc s :=
    (L.isColimit ⊤).desc
      { pt := s.pt
        ι :=
          { app a := s.ι.app a.1
            naturality a b f := by
              change Y.map (homOfLE (leOfHom f)) ≫ s.ι.app b.1 =
                s.ι.app a.1 ≫ 𝟙 _
              simpa only [Category.comp_id] using s.w (homOfLE (leOfHom f)) } }
  fac s a := (L.isColimit ⊤).fac _ ⟨a, by simp⟩
  uniq s m hm := by
    apply L.hom_ext
    intro a
    rw [(L.isColimit ⊤).fac]
    exact hm a.1

section Union

variable {B D : LowerSet P} {Z : C}
  (u : L.obj B ⟶ Z) (v : L.obj D ⟶ Z)
  (h : L.map inf_le_left ≫ u = L.map inf_le_right ≫ v)

include h in
/-- Agreement of the original vertex functions on the label intersection. -/
theorem intersection_leg_eq (a : P) (haB : a ∈ B) (haD : a ∈ D) :
    L.ι B ⟨a, haB⟩ ≫ u = L.ι D ⟨a, haD⟩ ≫ v := by
  have hh := congrArg
    (fun k => L.ι (B ⊓ D) ⟨a, ⟨haB, haD⟩⟩ ≫ k) h
  simpa only [← Category.assoc, ι_map] using hh

/-- A glued vertex function, choosing the first lower piece when available. -/
def unionApp (a : ↥(B ⊔ D)) : Y.obj a.1 ⟶ Z := by
  classical
  exact if ha : a.1 ∈ B then L.ι B ⟨a.1, ha⟩ ≫ u
    else L.ι D ⟨a.1, by
      have hh : a.1 ∈ B ∨ a.1 ∈ D := LowerSet.mem_sup_iff.1 a.2
      exact hh.resolve_left ha⟩ ≫ v

theorem unionApp_of_mem_left (a : ↥(B ⊔ D)) (ha : a.1 ∈ B) :
    L.unionApp u v a = L.ι B ⟨a.1, ha⟩ ≫ u := by
  classical
  simp only [unionApp, dite_eq_left ha]

include h in
theorem unionApp_of_mem_right (a : ↥(B ⊔ D)) (ha : a.1 ∈ D) :
    L.unionApp u v a = L.ι D ⟨a.1, ha⟩ ≫ v := by
  classical
  by_cases haB : a.1 ∈ B
  · rw [L.unionApp_of_mem_left u v a haB]
    exact L.intersection_leg_eq u v h a.1 haB ha
  · simp only [unionApp, dite_eq_right haB]

/-- The original lower cocones glue on their label union. -/
abbrev unionCocone : Cocone (restriction Y (B ⊔ D)) where
  pt := Z
  ι :=
    { app a := L.unionApp u v a
      naturality a b f := by
        change Y.map (homOfLE (leOfHom f)) ≫ L.unionApp u v b =
          L.unionApp u v a ≫ 𝟙 _
        rw [Category.comp_id]
        have hb : b.1 ∈ B ∨ b.1 ∈ D := LowerSet.mem_sup_iff.1 b.2
        rcases hb with hbB | hbD
        · have haB : a.1 ∈ B := B.lower (leOfHom f) hbB
          rw [L.unionApp_of_mem_left u v b hbB, L.unionApp_of_mem_left u v a haB]
          simpa only [restriction, inclusion, Functor.comp_map, ι, Category.assoc] using
            ((L.cocone B).w
              (homOfLE (leOfHom f) :
                (⟨a.1, haB⟩ : B) ⟶ (⟨b.1, hbB⟩ : B))) =≫ u
        · have haD : a.1 ∈ D := D.lower (leOfHom f) hbD
          rw [L.unionApp_of_mem_right u v h b hbD,
            L.unionApp_of_mem_right u v h a haD]
          simpa only [restriction, inclusion, Functor.comp_map, ι, Category.assoc] using
            ((L.cocone D).w
              (homOfLE (leOfHom f) :
                (⟨a.1, haD⟩ : D) ⟶ (⟨b.1, hbD⟩ : D))) =≫ v }

/-- The actual lower-union desc map. -/
abbrev unionDesc : L.obj (B ⊔ D) ⟶ Z :=
  (L.isColimit (B ⊔ D)).desc (L.unionCocone u v h)

@[reassoc]
theorem map_left_unionDesc : L.map le_sup_left ≫ L.unionDesc u v h = u := by
  apply L.hom_ext
  intro a
  rw [ι_map_assoc, (L.isColimit (B ⊔ D)).fac]
  exact L.unionApp_of_mem_left u v ⟨a.1, Or.inl a.2⟩ a.2

@[reassoc]
theorem map_right_unionDesc : L.map le_sup_right ≫ L.unionDesc u v h = v := by
  apply L.hom_ext
  intro a
  rw [ι_map_assoc, (L.isColimit (B ⊔ D)).fac]
  exact L.unionApp_of_mem_right u v h ⟨a.1, Or.inr a.2⟩ a.2

end Union

/-- All four actual lower comparison functions form the label-union pushout. -/
theorem union_isPushout (B D : LowerSet P) :
    IsPushout (L.map (inf_le_left : B ⊓ D ≤ B))
      (L.map (inf_le_right : B ⊓ D ≤ D))
      (L.map (le_sup_left : B ≤ B ⊔ D)) (L.map (le_sup_right : D ≤ B ⊔ D)) := by
  have hs : L.map (inf_le_left : B ⊓ D ≤ B) ≫ L.map le_sup_left =
      L.map (inf_le_right : B ⊓ D ≤ D) ≫ L.map le_sup_right := by
    rw [L.map_comp, L.map_comp]
  refine ⟨⟨hs⟩, ⟨PushoutCocone.IsColimit.mk hs ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact L.unionDesc s.inl s.inr s.condition
  · intro s
    exact L.map_left_unionDesc s.inl s.inr s.condition
  · intro s
    exact L.map_right_unionDesc s.inl s.inr s.condition
  · intro s m hB hD
    apply L.hom_ext
    intro a
    have ha : a.1 ∈ B ∨ a.1 ∈ D := LowerSet.mem_sup_iff.1 a.2
    rcases ha with haB | haD
    · calc
        L.ι (B ⊔ D) a ≫ m =
            L.ι B ⟨a.1, haB⟩ ≫ (L.map le_sup_left ≫ m) :=
          (L.ι_map_assoc (le_sup_left : B ≤ B ⊔ D) ⟨a.1, haB⟩ m).symm
        _ = L.ι B ⟨a.1, haB⟩ ≫ s.inl := by rw [hB]
        _ = L.ι B ⟨a.1, haB⟩ ≫
            (L.map le_sup_left ≫ L.unionDesc s.inl s.inr s.condition) :=
          congrArg (fun k => L.ι B ⟨a.1, haB⟩ ≫ k)
            (L.map_left_unionDesc s.inl s.inr s.condition).symm
        _ = L.ι (B ⊔ D) a ≫ L.unionDesc s.inl s.inr s.condition :=
          L.ι_map_assoc (le_sup_left : B ≤ B ⊔ D) ⟨a.1, haB⟩ _
    · calc
        L.ι (B ⊔ D) a ≫ m =
            L.ι D ⟨a.1, haD⟩ ≫ (L.map le_sup_right ≫ m) :=
          (L.ι_map_assoc (le_sup_right : D ≤ B ⊔ D) ⟨a.1, haD⟩ m).symm
        _ = L.ι D ⟨a.1, haD⟩ ≫ s.inr := by rw [hD]
        _ = L.ι D ⟨a.1, haD⟩ ≫
            (L.map le_sup_right ≫ L.unionDesc s.inl s.inr s.condition) :=
          congrArg (fun k => L.ι D ⟨a.1, haD⟩ ≫ k)
            (L.map_right_unionDesc s.inl s.inr s.condition).symm
        _ = L.ι (B ⊔ D) a ≫ L.unionDesc s.inl s.inr s.condition :=
          L.ι_map_assoc (le_sup_right : D ≤ B ⊔ D) ⟨a.1, haD⟩ _

section Filtered

variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
  (B : I ⥤ LowerSet P)

/-- The label union of an actual filtered diagram of lower sets. -/
abbrev filteredUnion : LowerSet P := ⨆ i, B.obj i

/-- The actual selected piece diagram. -/
abbrev filteredDiagram : I ⥤ C := B ⋙ L.functor

/-- Its original comparison cocone to the label union. -/
abbrev filteredCocone : Cocone (L.filteredDiagram B) where
  pt := L.obj (filteredUnion B)
  ι :=
    { app i := L.map (le_iSup (fun j => B.obj j) i)
      naturality i j f := by
        change L.map (leOfHom (B.map f)) ≫ L.map _ = L.map _ ≫ 𝟙 _
        rw [Category.comp_id, L.map_comp] }

variable {B}

/-- Every original union label has an actual selected stage. -/
def unionIndex (a : filteredUnion B) : I :=
  Classical.choose (show ∃ i, a.1 ∈ B.obj i from by
    simpa only [filteredUnion, LowerSet.mem_iSup_iff] using a.2)

omit [IsFiltered I] in
theorem mem_unionIndex (a : filteredUnion B) :
    a.1 ∈ B.obj (unionIndex a) :=
  Classical.choose_spec (show ∃ i, a.1 ∈ B.obj i from by
    simpa only [filteredUnion, LowerSet.mem_iSup_iff] using a.2)

/-- The filtered cocone has the same original vertex function at any stage containing it. -/
theorem filtered_leg_eq (s : Cocone (L.filteredDiagram B)) (a : P)
    (i j : I) (hai : a ∈ B.obj i) (haj : a ∈ B.obj j) :
    L.ι (B.obj i) ⟨a, hai⟩ ≫ s.ι.app i =
      L.ι (B.obj j) ⟨a, haj⟩ ≫ s.ι.app j := by
  let m := IsFiltered.max i j
  let fi := IsFiltered.leftToMax i j
  let fj := IsFiltered.rightToMax i j
  have hi := (s.w fi).symm
  have hj := (s.w fj).symm
  rw [hi, hj]
  change L.ι (B.obj i) ⟨a, hai⟩ ≫ (L.map (leOfHom (B.map fi)) ≫ s.ι.app m) =
    L.ι (B.obj j) ⟨a, haj⟩ ≫ (L.map (leOfHom (B.map fj)) ≫ s.ι.app m)
  rw [← Category.assoc, ι_map, ← Category.assoc, ι_map]

/-- A whole original vertex function for the filtered label union. -/
def filteredApp (s : Cocone (L.filteredDiagram B)) (a : filteredUnion B) :
    Y.obj a.1 ⟶ s.pt :=
  L.ι (B.obj (unionIndex a)) ⟨a.1, mem_unionIndex a⟩ ≫ s.ι.app (unionIndex a)

theorem filteredApp_eq (s : Cocone (L.filteredDiagram B))
    (a : filteredUnion B) (i : I) (ha : a.1 ∈ B.obj i) :
    L.filteredApp s a = L.ι (B.obj i) ⟨a.1, ha⟩ ≫ s.ι.app i :=
  L.filtered_leg_eq s a.1 (unionIndex a) i (mem_unionIndex a) ha

/-- The filtered stage functions glue as a cocone on the original union labels. -/
abbrev filteredVertexCocone (s : Cocone (L.filteredDiagram B)) :
    Cocone (restriction Y (filteredUnion B)) where
  pt := s.pt
  ι :=
    { app a := L.filteredApp s a
      naturality a b f := by
        let i := unionIndex b
        have hb : b.1 ∈ B.obj i := mem_unionIndex b
        have ha : a.1 ∈ B.obj i := (B.obj i).lower (leOfHom f) hb
        change Y.map (homOfLE (leOfHom f)) ≫ L.filteredApp s b =
          L.filteredApp s a ≫ 𝟙 _
        rw [Category.comp_id, L.filteredApp_eq s b i hb, L.filteredApp_eq s a i ha]
        simpa only [restriction, inclusion, Functor.comp_map, ι, Category.assoc] using
          ((L.cocone (B.obj i)).w
            (homOfLE (leOfHom f) :
              (⟨a.1, ha⟩ : B.obj i) ⟶ (⟨b.1, hb⟩ : B.obj i))) =≫ s.ι.app i }

/-- The exact filtered-union colimit desc. -/
abbrev filteredDesc (s : Cocone (L.filteredDiagram B)) :
    L.obj (filteredUnion B) ⟶ s.pt :=
  (L.isColimit (filteredUnion B)).desc (L.filteredVertexCocone s)

theorem filteredDesc_fac (s : Cocone (L.filteredDiagram B)) (i : I) :
    (L.filteredCocone B).ι.app i ≫ L.filteredDesc s = s.ι.app i := by
  apply L.hom_ext
  intro a
  rw [ι_map_assoc, (L.isColimit (filteredUnion B)).fac]
  exact L.filteredApp_eq s ⟨a.1, memOfLE (le_iSup (fun j => B.obj j) i) a.2⟩ i a.2

/-- The actual label-union cocone is colimit for every filtered stage category. -/
def isColimitFilteredCocone : IsColimit (L.filteredCocone B) where
  desc s := L.filteredDesc s
  fac s i := L.filteredDesc_fac s i
  uniq s m hm := by
    apply L.hom_ext
    intro a
    let i := unionIndex a
    have ha : a.1 ∈ B.obj i := mem_unionIndex a
    calc
      L.ι (filteredUnion B) a ≫ m =
          L.ι (B.obj i) ⟨a.1, ha⟩ ≫ ((L.filteredCocone B).ι.app i ≫ m) :=
        (L.ι_map_assoc (le_iSup (fun j => B.obj j) i) ⟨a.1, ha⟩ m).symm
      _ = L.ι (B.obj i) ⟨a.1, ha⟩ ≫ s.ι.app i := by rw [hm i]
      _ = L.ι (B.obj i) ⟨a.1, ha⟩ ≫
          ((L.filteredCocone B).ι.app i ≫ L.filteredDesc s) :=
        congrArg (fun k => L.ι (B.obj i) ⟨a.1, ha⟩ ≫ k) (L.filteredDesc_fac s i).symm
      _ = L.ι (filteredUnion B) a ≫ L.filteredDesc s :=
        L.ι_map_assoc (le_iSup (fun j => B.obj j) i) ⟨a.1, ha⟩ _

end Filtered

end LowerSetColimitData

end CategoryTheory.SmallObject
