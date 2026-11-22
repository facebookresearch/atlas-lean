/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Gluing the original selected lower colimits

Only the displayed restricted colimit cocones are used. In particular, two
equal lower label sets may carry different original colimit objects. The
comparison maps, whole pushout descenders and filtered-union cocones retain
those choices. Neither global colimits nor a model structure are required.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w v u vI uI

namespace CategoryTheory.SmallObject.SelectedLowerColimits

open CategoryTheory.Limits LowerSetColimits

variable {P : Type w} [Preorder P] {C : Type u} [Category.{v} C]
  {Y : P ⥤ C}

/-- Restrict this original cocone along the actual lower-label inclusion. -/
abbrev restrictCocone {B D : LowerSet P} (h : B ≤ D)
    (d : Cocone (restriction Y D)) : Cocone (restriction Y B) where
  pt := d.pt
  ι :=
    { app a := d.ι.app ⟨a.1, memOfLE h a.2⟩
      naturality a b f := by
        change Y.map (homOfLE (leOfHom f)) ≫ d.ι.app ⟨b.1, memOfLE h b.2⟩ =
          d.ι.app ⟨a.1, memOfLE h a.2⟩ ≫ 𝟙 _
        simpa only [restriction, inclusion, Functor.comp_map, Category.comp_id] using
          d.w (homOfLE (leOfHom f) :
            (⟨a.1, memOfLE h a.2⟩ : D) ⟶ (⟨b.1, memOfLE h b.2⟩ : D)) }

/-- The actual comparison of these two chosen lower colimits. -/
abbrev map {B D : LowerSet P} (h : B ≤ D)
    (b : ColimitCocone (restriction Y B)) (d : ColimitCocone (restriction Y D)) :
    b.cocone.pt ⟶ d.cocone.pt :=
  b.isColimit.desc (restrictCocone h d.cocone)

@[reassoc]
theorem ι_map {B D : LowerSet P} (h : B ≤ D)
    (b : ColimitCocone (restriction Y B)) (d : ColimitCocone (restriction Y D))
    (a : B) :
    b.cocone.ι.app a ≫ map h b d = d.cocone.ι.app ⟨a.1, memOfLE h a.2⟩ :=
  b.isColimit.fac (restrictCocone h d.cocone) a

@[reassoc]
theorem map_id {B : LowerSet P} (b : ColimitCocone (restriction Y B)) :
    map (le_refl B) b b = 𝟙 b.cocone.pt := by
  apply b.isColimit.hom_ext
  intro a
  simp only [ι_map, Category.comp_id]

@[reassoc]
theorem map_comp {B D E : LowerSet P} (hBD : B ≤ D) (hDE : D ≤ E)
    (b : ColimitCocone (restriction Y B)) (d : ColimitCocone (restriction Y D))
    (e : ColimitCocone (restriction Y E)) :
    map hBD b d ≫ map hDE d e = map (hBD.trans hDE) b e := by
  apply b.isColimit.hom_ext
  intro a
  rw [ι_map_assoc, ι_map, ι_map]

/-- Agreement with every actual original all-lower comparison, as a whole function. -/
theorem map_function_agrees (L : LowerSetColimitData Y) :
    (fun (B D : LowerSet P) (h : B ≤ D) =>
      map h ⟨L.cocone B, L.isColimit B⟩ ⟨L.cocone D, L.isColimit D⟩) =
    (fun (B D : LowerSet P) (h : B ≤ D) => L.map h) := by
  funext B D h
  apply (L.isColimit B).hom_ext
  intro a
  exact (ι_map h ⟨L.cocone B, L.isColimit B⟩
    ⟨L.cocone D, L.isColimit D⟩ a).trans (L.ι_map h a).symm

/-- Exactly the four chosen restricted colimits involved in a lower-label union. -/
structure UnionColimitData (Y : P ⥤ C) (B D : LowerSet P) where
  /-- The original colimit on the first lower label set. -/
  left : ColimitCocone (restriction Y B)
  /-- The original colimit on the second lower label set. -/
  right : ColimitCocone (restriction Y D)
  /-- The original colimit on their label intersection. -/
  intersection : ColimitCocone (restriction Y (B ⊓ D))
  /-- The original colimit on their label union. -/
  union : ColimitCocone (restriction Y (B ⊔ D))

namespace UnionColimitData

variable {B D : LowerSet P} (Q : UnionColimitData Y B D)

/-- The original intersection-to-first-piece function. -/
abbrev intersectionToLeft : Q.intersection.cocone.pt ⟶ Q.left.cocone.pt :=
  map inf_le_left Q.intersection Q.left

/-- The original intersection-to-second-piece function. -/
abbrev intersectionToRight : Q.intersection.cocone.pt ⟶ Q.right.cocone.pt :=
  map inf_le_right Q.intersection Q.right

/-- The original first-piece-to-union function. -/
abbrev leftToUnion : Q.left.cocone.pt ⟶ Q.union.cocone.pt :=
  map le_sup_left Q.left Q.union

/-- The original second-piece-to-union function. -/
abbrev rightToUnion : Q.right.cocone.pt ⟶ Q.union.cocone.pt :=
  map le_sup_right Q.right Q.union

/-- The complete original four-map square commutes. -/
theorem square :
    Q.intersectionToLeft ≫ Q.leftToUnion =
      Q.intersectionToRight ≫ Q.rightToUnion := by
  rw [map_comp, map_comp]

section Descender

variable {Z : C} (f : Q.left.cocone.pt ⟶ Z) (g : Q.right.cocone.pt ⟶ Z)
  (h : Q.intersectionToLeft ≫ f = Q.intersectionToRight ≫ g)

include h in
/-- The two given maps agree at every original intersection label. -/
theorem intersectionLegEq (a : P) (haB : a ∈ B) (haD : a ∈ D) :
    Q.left.cocone.ι.app ⟨a, haB⟩ ≫ f =
      Q.right.cocone.ι.app ⟨a, haD⟩ ≫ g := by
  have hh := congrArg
    (fun k => Q.intersection.cocone.ι.app ⟨a, ⟨haB, haD⟩⟩ ≫ k) h
  simpa only [← Category.assoc, ι_map] using hh

/-- The original glued vertex function on the lower-label union. -/
def unionApp (a : ↥(B ⊔ D)) : Y.obj a.1 ⟶ Z := by
  classical
  exact if ha : a.1 ∈ B then Q.left.cocone.ι.app ⟨a.1, ha⟩ ≫ f
    else Q.right.cocone.ι.app ⟨a.1, by
      have hh : a.1 ∈ B ∨ a.1 ∈ D := LowerSet.mem_sup_iff.1 a.2
      exact hh.resolve_left ha⟩ ≫ g

theorem unionAppOfMemLeft (a : ↥(B ⊔ D)) (ha : a.1 ∈ B) :
    Q.unionApp f g a = Q.left.cocone.ι.app ⟨a.1, ha⟩ ≫ f := by
  classical
  simp only [unionApp, dite_eq_left ha]

include h in
theorem unionAppOfMemRight (a : ↥(B ⊔ D)) (ha : a.1 ∈ D) :
    Q.unionApp f g a = Q.right.cocone.ι.app ⟨a.1, ha⟩ ≫ g := by
  classical
  by_cases haB : a.1 ∈ B
  · rw [Q.unionAppOfMemLeft f g a haB]
    exact Q.intersectionLegEq f g h a.1 haB ha
  · simp only [unionApp, dite_eq_right haB]

/-- The two original cocones glue over precisely their lower-label union. -/
abbrev unionCocone : Cocone (restriction Y (B ⊔ D)) where
  pt := Z
  ι :=
    { app a := Q.unionApp f g a
      naturality a b k := by
        change Y.map (homOfLE (leOfHom k)) ≫ Q.unionApp f g b =
          Q.unionApp f g a ≫ 𝟙 _
        rw [Category.comp_id]
        have hb : b.1 ∈ B ∨ b.1 ∈ D := LowerSet.mem_sup_iff.1 b.2
        rcases hb with hbB | hbD
        · have haB : a.1 ∈ B := B.lower (leOfHom k) hbB
          rw [Q.unionAppOfMemLeft f g b hbB, Q.unionAppOfMemLeft f g a haB]
          simpa only [restriction, inclusion, Functor.comp_map, Category.assoc] using
            (Q.left.cocone.w
              (homOfLE (leOfHom k) :
                (⟨a.1, haB⟩ : B) ⟶ (⟨b.1, hbB⟩ : B))) =≫ f
        · have haD : a.1 ∈ D := D.lower (leOfHom k) hbD
          rw [Q.unionAppOfMemRight f g h b hbD, Q.unionAppOfMemRight f g h a haD]
          simpa only [restriction, inclusion, Functor.comp_map, Category.assoc] using
            (Q.right.cocone.w
              (homOfLE (leOfHom k) :
                (⟨a.1, haD⟩ : D) ⟶ (⟨b.1, hbD⟩ : D))) =≫ g }

/-- The full original union descender, retaining the selected union colimit. -/
abbrev unionDesc : Q.union.cocone.pt ⟶ Z :=
  Q.union.isColimit.desc (Q.unionCocone f g h)

@[reassoc]
theorem leftToUnion_desc : Q.leftToUnion ≫ Q.unionDesc f g h = f := by
  apply Q.left.isColimit.hom_ext
  intro a
  rw [ι_map_assoc, Q.union.isColimit.fac]
  exact Q.unionAppOfMemLeft f g ⟨a.1, Or.inl a.2⟩ a.2

@[reassoc]
theorem rightToUnion_desc : Q.rightToUnion ≫ Q.unionDesc f g h = g := by
  apply Q.right.isColimit.hom_ext
  intro a
  rw [ι_map_assoc, Q.union.isColimit.fac]
  exact Q.unionAppOfMemRight f g h ⟨a.1, Or.inr a.2⟩ a.2

end Descender

/-- Maps out of the original union are detected by the two selected piece maps. -/
theorem hom_ext {Z : C} {f g : Q.union.cocone.pt ⟶ Z}
    (hB : Q.leftToUnion ≫ f = Q.leftToUnion ≫ g)
    (hD : Q.rightToUnion ≫ f = Q.rightToUnion ≫ g) : f = g := by
  apply Q.union.isColimit.hom_ext
  intro a
  rcases LowerSet.mem_sup_iff.1 a.2 with haB | haD
  · have hh := congrArg (fun k => Q.left.cocone.ι.app ⟨a.1, haB⟩ ≫ k) hB
    simpa only [← Category.assoc, ι_map] using hh
  · have hh := congrArg (fun k => Q.right.cocone.ι.app ⟨a.1, haD⟩ ≫ k) hD
    simpa only [← Category.assoc, ι_map] using hh

/-- These four actual restricted colimits form a pushout; no other colimit is an input. -/
theorem isPushout :
    IsPushout Q.intersectionToLeft Q.intersectionToRight
      Q.leftToUnion Q.rightToUnion := by
  refine ⟨⟨Q.square⟩, ⟨PushoutCocone.IsColimit.mk Q.square ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact Q.unionDesc s.inl s.inr s.condition
  · intro s
    exact Q.leftToUnion_desc s.inl s.inr s.condition
  · intro s
    exact Q.rightToUnion_desc s.inl s.inr s.condition
  · intro s m hB hD
    exact Q.hom_ext (hB.trans (Q.leftToUnion_desc s.inl s.inr s.condition).symm)
      (hD.trans (Q.rightToUnion_desc s.inl s.inr s.condition).symm)

/-- Forgetting an original under-root union preserves the actual connected pushout. -/
theorem underlyingIsPushout {X : C} {Y : P ⥤ Under X}
    (Q : UnionColimitData Y B D) :
    IsPushout Q.intersectionToLeft.right Q.intersectionToRight.right
      Q.leftToUnion.right Q.rightToUnion.right :=
  Q.isPushout.map (Under.forget X)

/-- Construct exactly these four original choices from an already given all-lower family. -/
abbrev ofAllLower (L : LowerSetColimitData Y) (B D : LowerSet P) :
    UnionColimitData Y B D where
  left := ⟨L.cocone B, L.isColimit B⟩
  right := ⟨L.cocone D, L.isColimit D⟩
  intersection := ⟨L.cocone (B ⊓ D), L.isColimit (B ⊓ D)⟩
  union := ⟨L.cocone (B ⊔ D), L.isColimit (B ⊔ D)⟩

end UnionColimitData

/-- A selected empty lower colimit is initial, regardless of the ambient category. -/
def emptyIsInitial (c : ColimitCocone (restriction Y (⊥ : LowerSet P))) :
    IsInitial c.cocone.pt :=
  IsInitial.ofUniqueHom
    (fun Z => c.isColimit.desc (LowerSetColimitData.emptyCocone (Y := Y) Z))
    (fun _ _ => c.isColimit.hom_ext (fun a => False.elim (LowerSet.notMem_bot a.2)))

/-- The selected empty under-root colimit has both original identity-root comparison maps. -/
def emptyUnderIso {X : C} {Y : P ⥤ Under X}
    (c : ColimitCocone (restriction Y (⊥ : LowerSet P))) :
    c.cocone.pt ≅ Under.mk (𝟙 X) :=
  (emptyIsInitial c).uniqueUpToIso Under.mkIdInitial

@[reassoc]
theorem emptyUnderIso_root {X : C} {Y : P ⥤ Under X}
    (c : ColimitCocone (restriction Y (⊥ : LowerSet P))) :
    c.cocone.pt.hom ≫ (emptyUnderIso c).hom.right = 𝟙 X :=
  Under.w (emptyUnderIso c).hom

/-- Only original stage colimits and the original union colimit are selected. -/
structure FilteredColimitData {I : Type uI} [Category.{vI} I]
    (Y : P ⥤ C) (B : I ⥤ LowerSet P) where
  /-- The actual chosen colimit of each displayed lower restriction. -/
  stage (i : I) : ColimitCocone (restriction Y (B.obj i))
  /-- The actual chosen colimit of the displayed lower-label union. -/
  union : ColimitCocone (restriction Y (LowerSetColimitData.filteredUnion B))

namespace FilteredColimitData

variable {I : Type uI} [Category.{vI} I] {B : I ⥤ LowerSet P}
  (Q : FilteredColimitData Y B)

/-- The original selected stage objects and comparison functions form a functor. -/
abbrev diagram : I ⥤ C where
  obj i := (Q.stage i).cocone.pt
  map {i j} f := map (leOfHom (B.map f)) (Q.stage i) (Q.stage j)
  map_id i := map_id (Q.stage i)
  map_comp {i j k} f g :=
    (map_comp (leOfHom (B.map f)) (leOfHom (B.map g))
      (Q.stage i) (Q.stage j) (Q.stage k)).symm

/-- The original stage-to-union maps form their actual comparison cocone. -/
abbrev cocone : Cocone Q.diagram where
  pt := Q.union.cocone.pt
  ι :=
    { app i := map (le_iSup (fun j => B.obj j) i) (Q.stage i) Q.union
      naturality i j f := by
        change map (leOfHom (B.map f)) (Q.stage i) (Q.stage j) ≫
          map _ (Q.stage j) Q.union =
          map _ (Q.stage i) Q.union ≫ 𝟙 _
        rw [Category.comp_id, map_comp] }

section Filtered

variable [IsFiltered I]

/-- A stage cocone has the same original vertex function at every containing stage. -/
theorem stageLegEq (s : Cocone Q.diagram) (a : P)
    (i j : I) (hai : a ∈ B.obj i) (haj : a ∈ B.obj j) :
    (Q.stage i).cocone.ι.app ⟨a, hai⟩ ≫ s.ι.app i =
      (Q.stage j).cocone.ι.app ⟨a, haj⟩ ≫ s.ι.app j := by
  let m := IsFiltered.max i j
  let fi := IsFiltered.leftToMax i j
  let fj := IsFiltered.rightToMax i j
  have hi := (s.w fi).symm
  have hj := (s.w fj).symm
  rw [hi, hj]
  change (Q.stage i).cocone.ι.app ⟨a, hai⟩ ≫
      (map (leOfHom (B.map fi)) (Q.stage i) (Q.stage m) ≫ s.ι.app m) =
    (Q.stage j).cocone.ι.app ⟨a, haj⟩ ≫
      (map (leOfHom (B.map fj)) (Q.stage j) (Q.stage m) ≫ s.ι.app m)
  rw [← Category.assoc, ι_map, ← Category.assoc, ι_map]

/-- The original containing-stage choice yields a whole union vertex function. -/
def unionApp (s : Cocone Q.diagram)
    (a : LowerSetColimitData.filteredUnion B) : Y.obj a.1 ⟶ s.pt :=
  (Q.stage (LowerSetColimitData.unionIndex a)).cocone.ι.app
      ⟨a.1, LowerSetColimitData.mem_unionIndex a⟩ ≫
    s.ι.app (LowerSetColimitData.unionIndex a)

theorem unionApp_eq (s : Cocone Q.diagram)
    (a : LowerSetColimitData.filteredUnion B) (i : I) (ha : a.1 ∈ B.obj i) :
    Q.unionApp s a = (Q.stage i).cocone.ι.app ⟨a.1, ha⟩ ≫ s.ι.app i :=
  Q.stageLegEq s a.1 (LowerSetColimitData.unionIndex a) i
    (LowerSetColimitData.mem_unionIndex a) ha

/-- The original filtered stage functions glue on the actual union labels. -/
abbrev unionVertexCocone (s : Cocone Q.diagram) :
    Cocone (restriction Y (LowerSetColimitData.filteredUnion B)) where
  pt := s.pt
  ι :=
    { app a := Q.unionApp s a
      naturality a b f := by
        let i := LowerSetColimitData.unionIndex b
        have hb : b.1 ∈ B.obj i := LowerSetColimitData.mem_unionIndex b
        have ha : a.1 ∈ B.obj i := (B.obj i).lower (leOfHom f) hb
        change Y.map (homOfLE (leOfHom f)) ≫ Q.unionApp s b =
          Q.unionApp s a ≫ 𝟙 _
        rw [Category.comp_id, Q.unionApp_eq s b i hb, Q.unionApp_eq s a i ha]
        simpa only [restriction, inclusion, Functor.comp_map, Category.assoc] using
          ((Q.stage i).cocone.w
            (homOfLE (leOfHom f) :
              (⟨a.1, ha⟩ : B.obj i) ⟶ (⟨b.1, hb⟩ : B.obj i))) =≫ s.ι.app i }

/-- The full actual union descender of the same original filtered stage cocone. -/
abbrev desc (s : Cocone Q.diagram) : Q.union.cocone.pt ⟶ s.pt :=
  Q.union.isColimit.desc (Q.unionVertexCocone s)

@[reassoc]
theorem cocone_desc (s : Cocone Q.diagram) (i : I) :
    Q.cocone.ι.app i ≫ Q.desc s = s.ι.app i := by
  apply (Q.stage i).isColimit.hom_ext
  intro a
  rw [ι_map_assoc, Q.union.isColimit.fac]
  exact Q.unionApp_eq s
    ⟨a.1, memOfLE (le_iSup (fun j => B.obj j) i) a.2⟩ i a.2

/-- The original selected union cocone is colimit for every filtered stage category. -/
def isColimit : IsColimit Q.cocone where
  desc s := Q.desc s
  fac s i := Q.cocone_desc s i
  uniq s m hm := by
    apply Q.union.isColimit.hom_ext
    intro a
    let i := LowerSetColimitData.unionIndex a
    have ha : a.1 ∈ B.obj i := LowerSetColimitData.mem_unionIndex a
    calc
      Q.union.cocone.ι.app a ≫ m =
          (Q.stage i).cocone.ι.app ⟨a.1, ha⟩ ≫ (Q.cocone.ι.app i ≫ m) :=
        (ι_map_assoc (le_iSup (fun j => B.obj j) i) (Q.stage i) Q.union ⟨a.1, ha⟩ m).symm
      _ = (Q.stage i).cocone.ι.app ⟨a.1, ha⟩ ≫ s.ι.app i := by rw [hm i]
      _ = (Q.stage i).cocone.ι.app ⟨a.1, ha⟩ ≫ (Q.cocone.ι.app i ≫ Q.desc s) :=
        congrArg (fun k => (Q.stage i).cocone.ι.app ⟨a.1, ha⟩ ≫ k)
          (Q.cocone_desc s i).symm
      _ = Q.union.cocone.ι.app a ≫ Q.desc s :=
        ι_map_assoc (le_iSup (fun j => B.obj j) i) (Q.stage i) Q.union ⟨a.1, ha⟩ _

end Filtered

/-- Select only these stages and this union from the supplied original all-lower family. -/
abbrev ofAllLower (L : LowerSetColimitData Y) (B : I ⥤ LowerSet P) :
    FilteredColimitData Y B where
  stage i := ⟨L.cocone (B.obj i), L.isColimit (B.obj i)⟩
  union := ⟨L.cocone (LowerSetColimitData.filteredUnion B),
    L.isColimit (LowerSetColimitData.filteredUnion B)⟩

end FilteredColimitData

end CategoryTheory.SmallObject.SelectedLowerColimits
