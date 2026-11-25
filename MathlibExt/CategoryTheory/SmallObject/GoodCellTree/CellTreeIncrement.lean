/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The original relative difference of two lower cell trees

The new labels are the literal original difference D \ B with its inherited
partial order. Its vertices and strict predecessors are the selected
colimits on B union the corresponding original principal lower pieces.
All colimits are constructed under the selected B endpoint. An empty
predecessor therefore retains the new identity root.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.CellTreeIncrement

open Limits LowerSetColimits

variable {P : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  {alpha : Type t} {s : alpha → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B D : LowerSet P) (hBD : B ≤ D)

/-- The literal original remaining labels; it is not an object intersection. -/
abbrev Label := CellTree.Increment B D

/-- Restore the original root labels to a lower piece of the difference. -/
abbrev expanded (Q : LowerSet (Label B D)) : LowerSet P :=
  ⟨{p | p ∈ B ∨ ∃ a : Label B D, a ∈ Q ∧ p ≤ a.1}, by
    intro p q hpq hq
    rcases hq with hqB | ⟨a, ha, hqa⟩
    · exact Or.inl (B.lower hpq hqB)
    · exact Or.inr ⟨a, ha, hpq.trans hqa⟩⟩

theorem mem_expanded_iff (Q : LowerSet (Label B D)) (p : P) :
    p ∈ expanded B D Q ↔ p ∈ B ∨ ∃ a : Label B D, a ∈ Q ∧ p ≤ a.1 := Iff.rfl

theorem base_le_expanded (Q : LowerSet (Label B D)) : B ≤ expanded B D Q := by
  intro p hp
  exact Or.inl hp

include hBD in
theorem expanded_le (Q : LowerSet (Label B D)) : expanded B D Q ≤ D := by
  intro p hp
  rcases hp with hpB | ⟨a, _, hpa⟩
  · exact memOfLE hBD hpB
  · exact D.lower hpa a.2.1

theorem expanded_mono {Q R : LowerSet (Label B D)} (h : Q ≤ R) :
    expanded B D Q ≤ expanded B D R := by
  intro p hp
  rcases hp with hpB | ⟨a, ha, hpa⟩
  · exact Or.inl hpB
  · exact Or.inr ⟨a, memOfLE h ha, hpa⟩

/-- Every original nonbase label in an expansion has its literal difference label. -/
def labelOfExpanded (Q : LowerSet (Label B D))
    (p : expanded B D Q) (hpB : p.1 ∉ B) : Label B D :=
  ⟨p.1, expanded_le B D hBD Q p.2, hpB⟩

theorem labelOfExpanded_mem (Q : LowerSet (Label B D))
    (p : expanded B D Q) (hpB : p.1 ∉ B) :
    labelOfExpanded B D hBD Q p hpB ∈ Q := by
  rcases p.2 with hp | ⟨a, ha, hpa⟩
  · exact False.elim (hpB hp)
  · exact Q.lower hpa ha

@[simp]
theorem expanded_bot : expanded B D ⊥ = B := by
  ext p
  constructor
  · intro hp
    rcases hp with hpB | ⟨a, ha, _⟩
    · exact hpB
    · exact False.elim (LowerSet.notMem_bot ha)
  · intro hp
    exact Or.inl hp

include hBD in
@[simp]
theorem expanded_top : expanded B D ⊤ = D := by
  apply le_antisymm (expanded_le B D hBD ⊤)
  intro p hpD
  by_cases hpB : p ∈ B
  · exact Or.inl hpB
  · exact Or.inr ⟨⟨p, hpD, hpB⟩, by trivial, le_rfl⟩

@[simp]
theorem expanded_Iic (a : Label B D) :
    expanded B D (LowerSet.Iic a) = B ⊔ LowerSet.Iic a.1 := by
  ext p
  constructor
  · intro hp
    rcases hp with hpB | ⟨b, hb, hpb⟩
    · exact Or.inl hpB
    · exact Or.inr (hpb.trans hb)
  · intro hp
    rcases hp with hpB | hpa
    · exact Or.inl hpB
    · exact Or.inr ⟨a, le_rfl, hpa⟩

@[simp]
theorem expanded_Iio (a : Label B D) :
    expanded B D (LowerSet.Iio a) = B ⊔ LowerSet.Iio a.1 := by
  ext p
  constructor
  · intro hp
    rcases hp with hpB | ⟨b, hb, hpb⟩
    · exact Or.inl hpB
    · exact Or.inr (lt_of_le_of_lt hpb hb)
  · intro hp
    rcases hp with hpB | hpa
    · exact Or.inl hpB
    · by_cases hpB : p ∈ B
      · exact Or.inl hpB
      · exact Or.inr ⟨⟨p, D.lower hpa.le a.2.1, hpB⟩, hpa, le_rfl⟩

/-- Expansion restricts to exactly the original lower labels of the difference. -/
theorem expanded_nonbase_iff (Q : LowerSet (Label B D)) (a : Label B D) :
    a.1 ∈ expanded B D Q ↔ a ∈ Q := by
  constructor
  · intro ha
    rcases ha with haB | ⟨b, hb, hab⟩
    · exact False.elim (a.2.2 haB)
    · exact Q.lower hab hb
  · intro ha
    exact Or.inr ⟨a, ha, le_rfl⟩

/-- The base label inclusion into every selected expanded piece. -/
abbrev rootMap (Q : LowerSet (Label B D)) :
    (L.obj B).right ⟶ (L.obj (expanded B D Q)).right :=
  (L.map (base_le_expanded B D Q)).right

/-- The selected original expanded piece under its actual new root. -/
abbrev obj (Q : LowerSet (Label B D)) : Under (L.obj B).right :=
  Under.mk (rootMap T L B D Q)

/-- Its actual selected inclusion function, promoted under the new root. -/
abbrev map {Q R : LowerSet (Label B D)} (h : Q ≤ R) :
    obj T L B D Q ⟶ obj T L B D R :=
  Under.homMk (L.map (expanded_mono B D h)).right (by
    change (L.map (base_le_expanded B D Q)).right ≫
      (L.map (expanded_mono B D h)).right = _
    exact congrArg Under.Hom.right
      (L.map_comp (base_le_expanded B D Q) (expanded_mono B D h)))

@[reassoc]
theorem map_comp {Q R S : LowerSet (Label B D)} (hQR : Q ≤ R) (hRS : R ≤ S) :
    map T L B D hQR ≫ map T L B D hRS = map T L B D (hQR.trans hRS) := by
  apply Under.UnderMorphism.ext
  change (L.map (expanded_mono B D hQR)).right ≫
    (L.map (expanded_mono B D hRS)).right =
      (L.map (expanded_mono B D (hQR.trans hRS))).right
  exact congrArg Under.Hom.right
    (L.map_comp (expanded_mono B D hQR) (expanded_mono B D hRS))

@[reassoc]
theorem map_id (Q : LowerSet (Label B D)) : map T L B D (le_refl Q) = 𝟙 (obj T L B D Q) := by
  apply Under.UnderMorphism.ext
  change (L.map (le_refl (expanded B D Q))).right = 𝟙 _
  exact congrArg Under.Hom.right (L.map_id (expanded B D Q))

/-- The original difference diagram has its same inherited order arrows. -/
abbrev diagram : Label B D ⥤ Under (L.obj B).right where
  obj a := obj T L B D (LowerSet.Iic a)
  map {a b} g := map T L B D (by
    intro p hp
    exact hp.trans (leOfHom g))
  map_id a := map_id T L B D (LowerSet.Iic a)
  map_comp f g := (map_comp T L B D _ _).symm

/-- A selected lower-piece cocone on the actual difference diagram. -/
abbrev cocone (Q : LowerSet (Label B D)) : Cocone (restriction (diagram T L B D) Q) where
  pt := obj T L B D Q
  ι :=
    { app a := map T L B D (by
        intro b hb
        exact Q.lower hb a.2)
      naturality a b g := by
        change map T L B D
          (show LowerSet.Iic a.1 ≤ LowerSet.Iic b.1 from fun z hz => hz.trans (leOfHom g)) ≫
          map T L B D (show LowerSet.Iic b.1 ≤ Q from fun z hz => Q.lower hz b.2) =
          map T L B D (show LowerSet.Iic a.1 ≤ Q from fun z hz => Q.lower hz a.2) ≫ 𝟙 _
        rw [Category.comp_id, map_comp] }

/-- Keep an object over the new root under the original root as well. -/
abbrev oldObject (Z : Under (L.obj B).right) : Under X :=
  (Under.map (L.obj B).hom).obj Z

/-- The actual new-root function as a morphism under the original root. -/
def baseToOld (Z : Under (L.obj B).right) : L.obj B ⟶ oldObject T L B Z :=
  Under.homMk Z.hom rfl

/-- A new-root map retains its original raw function when viewed under X. -/
abbrev toOld {Q : LowerSet (Label B D)} {Z : Under (L.obj B).right}
    (p : obj T L B D Q ⟶ Z) : L.obj (expanded B D Q) ⟶ oldObject T L B Z :=
  Under.homMk p.right (by
    change (L.obj (expanded B D Q)).hom ≫ p.right = (L.obj B).hom ≫ Z.hom
    rw [← Under.w (L.map (base_le_expanded B D Q)), Category.assoc]
    exact congrArg (fun k => (L.obj B).hom ≫ k) (Under.w p))

section Colimit

variable {Q : LowerSet (Label B D)} (c : Cocone (restriction (diagram T L B D) Q))

/-- Original vertex functions, using the actual base map or difference cocone leg. -/
def app (p : expanded B D Q) : T.diagram.obj p.1 ⟶ oldObject T L B c.pt := by
  classical
  exact if hpB : p.1 ∈ B then L.ι B ⟨p.1, hpB⟩ ≫ baseToOld T L B c.pt
    else
      let a := labelOfExpanded B D hBD Q p hpB
      let ha := labelOfExpanded_mem B D hBD Q p hpB
      L.ι (expanded B D (LowerSet.Iic a)) ⟨p.1, Or.inr ⟨a, le_rfl, le_rfl⟩⟩ ≫
        toOld T L B D (c.ι.app ⟨a, ha⟩)

theorem app_of_base (p : expanded B D Q) (hpB : p.1 ∈ B) :
    app T L B D hBD c p = L.ι B ⟨p.1, hpB⟩ ≫ baseToOld T L B c.pt := by
  classical
  simp only [app, dite_eq_left hpB]

/-- A nonbase vertex has the same function through any later difference vertex. -/
theorem app_through (p : expanded B D Q) (a : Q) (hpa : p.1 ≤ a.1.1) :
    app T L B D hBD c p =
      L.ι (expanded B D (LowerSet.Iic a.1))
        ⟨p.1, Or.inr ⟨a.1, le_rfl, hpa⟩⟩ ≫ toOld T L B D (c.ι.app a) := by
  classical
  by_cases hpB : p.1 ∈ B
  · rw [app_of_base T L B D hBD c p hpB]
    apply Under.UnderMorphism.ext
    change (L.ι B ⟨p.1, hpB⟩).right ≫ c.pt.hom =
      (L.ι (expanded B D (LowerSet.Iic a.1))
        ⟨p.1, Or.inr ⟨a.1, le_rfl, hpa⟩⟩).right ≫ (c.ι.app a).right
    have hh := Under.w (c.ι.app a)
    change (L.map (base_le_expanded B D (LowerSet.Iic a.1))).right ≫
      (c.ι.app a).right = c.pt.hom at hh
    rw [← hh, ← Category.assoc]
    exact congrArg (fun k : T.diagram.obj p.1 ⟶
        L.obj (expanded B D (LowerSet.Iic a.1)) => k.right ≫ (c.ι.app a).right)
      (L.ι_map (base_le_expanded B D (LowerSet.Iic a.1)) ⟨p.1, hpB⟩)
  · let b := labelOfExpanded B D hBD Q p hpB
    let hb := labelOfExpanded_mem B D hBD Q p hpB
    have hba : b ≤ a.1 := hpa
    have hw := congrArg Under.Hom.right
      (c.w (homOfLE hba : (⟨b, hb⟩ : Q) ⟶ a))
    change (L.map (expanded_mono B D
        (show LowerSet.Iic b ≤ LowerSet.Iic a.1 from fun z hz => hz.trans hba))).right ≫
        (c.ι.app a).right = (c.ι.app ⟨b, hb⟩).right at hw
    dsimp only [app]
    rw [dite_eq_right hpB]
    apply Under.UnderMorphism.ext
    change (L.ι (expanded B D (LowerSet.Iic b))
        ⟨p.1, Or.inr ⟨b, le_rfl, le_rfl⟩⟩).right ≫
      (c.ι.app ⟨b, hb⟩).right =
        (L.ι (expanded B D (LowerSet.Iic a.1))
          ⟨p.1, Or.inr ⟨a.1, le_rfl, hpa⟩⟩).right ≫ (c.ι.app a).right
    rw [← hw, ← Category.assoc]
    exact congrArg (fun k : T.diagram.obj p.1 ⟶
        L.obj (expanded B D (LowerSet.Iic a.1)) => k.right ≫ (c.ι.app a).right)
      (L.ι_map (expanded_mono B D
        (show LowerSet.Iic b ≤ LowerSet.Iic a.1 from fun z hz => hz.trans hba))
        ⟨p.1, Or.inr ⟨b, le_rfl, le_rfl⟩⟩)

/-- The actual maps glue over every original expanded label and order arrow. -/
abbrev originalCocone : Cocone (restriction T.diagram (expanded B D Q)) where
  pt := oldObject T L B c.pt
  ι :=
    { app p := app T L B D hBD c p
      naturality p q g := by
        change T.diagram.map (homOfLE (leOfHom g)) ≫ app T L B D hBD c q =
          app T L B D hBD c p ≫ 𝟙 _
        rw [Category.comp_id]
        by_cases hqB : q.1 ∈ B
        · have hpB := B.lower (leOfHom g) hqB
          rw [app_of_base T L B D hBD c q hqB,
            app_of_base T L B D hBD c p hpB, ← Category.assoc]
          exact congrArg (· ≫ baseToOld T L B c.pt)
            ((L.cocone B).w
              (homOfLE (leOfHom g) : (⟨p.1, hpB⟩ : B) ⟶ ⟨q.1, hqB⟩))
        · let a := labelOfExpanded B D hBD Q q hqB
          let ha := labelOfExpanded_mem B D hBD Q q hqB
          rw [app_through T L B D hBD c q ⟨a, ha⟩ le_rfl,
            app_through T L B D hBD c p ⟨a, ha⟩ (leOfHom g), ← Category.assoc]
          exact congrArg (· ≫ toOld T L B D (c.ι.app ⟨a, ha⟩))
            ((L.cocone (expanded B D (LowerSet.Iic a))).w
              (homOfLE (leOfHom g) :
                (⟨p.1, Or.inr ⟨a, le_rfl, leOfHom g⟩⟩ : expanded B D (LowerSet.Iic a)) ⟶
                  ⟨q.1, Or.inr ⟨a, le_rfl, le_rfl⟩⟩)) }

/-- The complete original chosen lower-colimit descender. -/
abbrev oldDesc : L.obj (expanded B D Q) ⟶ oldObject T L B c.pt :=
  (L.isColimit (expanded B D Q)).desc (originalCocone T L B D hBD c)

@[reassoc]
theorem oldDesc_fac (p : expanded B D Q) :
    L.ι (expanded B D Q) p ≫ oldDesc T L B D hBD c = app T L B D hBD c p :=
  (L.isColimit (expanded B D Q)).fac (originalCocone T L B D hBD c) p

/-- The new root equation is proved by the base colimit, including the empty case. -/
theorem base_oldDesc :
    L.map (base_le_expanded B D Q) ≫ oldDesc T L B D hBD c = baseToOld T L B c.pt := by
  apply L.hom_ext
  intro p
  rw [L.ι_map_assoc, oldDesc_fac]
  exact app_of_base T L B D hBD c _ p.2

/-- Promote the same original descender under the actual selected B endpoint. -/
def desc : obj T L B D Q ⟶ c.pt :=
  Under.homMk (oldDesc T L B D hBD c).right
    (congrArg Under.Hom.right (base_oldDesc T L B D hBD c))

/-- Every original difference vertex leg retains its exact selected descender equation. -/
theorem desc_fac (a : Q) :
    (cocone T L B D Q).ι.app a ≫ desc T L B D hBD c = c.ι.app a := by
  apply Under.UnderMorphism.ext
  have hh :
      L.map (expanded_mono B D
          (show LowerSet.Iic a.1 ≤ Q from fun b hb => Q.lower hb a.2)) ≫
        oldDesc T L B D hBD c = toOld T L B D (c.ι.app a) := by
    apply L.hom_ext
    intro p
    rw [L.ι_map_assoc, oldDesc_fac]
    rcases p.2 with hpB | ⟨b, hb, hpb⟩
    · rw [app_of_base T L B D hBD c _ hpB]
      apply Under.UnderMorphism.ext
      change (L.ι B ⟨p.1, hpB⟩).right ≫ c.pt.hom =
        (L.ι (expanded B D (LowerSet.Iic a.1)) p).right ≫ (c.ι.app a).right
      have hr := Under.w (c.ι.app a)
      change (L.map (base_le_expanded B D (LowerSet.Iic a.1))).right ≫
        (c.ι.app a).right = c.pt.hom at hr
      rw [← hr, ← Category.assoc]
      exact congrArg (fun k : T.diagram.obj p.1 ⟶
          L.obj (expanded B D (LowerSet.Iic a.1)) => k.right ≫ (c.ι.app a).right)
        (L.ι_map (base_le_expanded B D (LowerSet.Iic a.1)) ⟨p.1, hpB⟩)
    · exact app_through T L B D hBD c _ a (hpb.trans hb)
  change (L.map (expanded_mono B D
    (show LowerSet.Iic a.1 ≤ Q from fun b hb => Q.lower hb a.2))).right ≫
      (oldDesc T L B D hBD c).right = (c.ι.app a).right
  exact congrArg (fun k : L.obj (expanded B D (LowerSet.Iic a.1)) ⟶
    oldObject T L B c.pt => k.right) hh

/-- The original expanded labels detect uniqueness of a new-root descender. -/
theorem desc_uniq (m : obj T L B D Q ⟶ c.pt)
    (hm : ∀ a : Q, (cocone T L B D Q).ι.app a ≫ m = c.ι.app a) :
    m = desc T L B D hBD c := by
  apply Under.UnderMorphism.ext
  have hh : toOld T L B D m = oldDesc T L B D hBD c := by
    apply L.hom_ext
    intro p
    rw [oldDesc_fac]
    by_cases hpB : p.1 ∈ B
    · rw [app_of_base T L B D hBD c p hpB]
      apply Under.UnderMorphism.ext
      change (L.ι (expanded B D Q) p).right ≫ m.right =
        (L.ι B ⟨p.1, hpB⟩).right ≫ c.pt.hom
      have hr := Under.w m
      change (L.map (base_le_expanded B D Q)).right ≫ m.right = c.pt.hom at hr
      rw [← hr, ← Category.assoc]
      exact (congrArg (fun k : T.diagram.obj p.1 ⟶ L.obj (expanded B D Q) =>
        k.right ≫ m.right) (L.ι_map (base_le_expanded B D Q) ⟨p.1, hpB⟩)).symm
    · let a := labelOfExpanded B D hBD Q p hpB
      let ha := labelOfExpanded_mem B D hBD Q p hpB
      rw [app_through T L B D hBD c p ⟨a, ha⟩ le_rfl]
      apply Under.UnderMorphism.ext
      change (L.ι (expanded B D Q) p).right ≫ m.right =
        (L.ι (expanded B D (LowerSet.Iic a))
          ⟨p.1, Or.inr ⟨a, le_rfl, le_rfl⟩⟩).right ≫ (c.ι.app ⟨a, ha⟩).right
      have hma := congrArg Under.Hom.right (hm ⟨a, ha⟩)
      change (L.map (expanded_mono B D
          (show LowerSet.Iic a ≤ Q from fun b hb => Q.lower hb ha))).right ≫
        m.right = (c.ι.app ⟨a, ha⟩).right at hma
      rw [← hma, ← Category.assoc]
      exact (congrArg (fun k : T.diagram.obj p.1 ⟶ L.obj (expanded B D Q) =>
          k.right ≫ m.right)
        (L.ι_map (expanded_mono B D
          (show LowerSet.Iic a ≤ Q from fun b hb => Q.lower hb ha))
          ⟨p.1, Or.inr ⟨a, le_rfl, le_rfl⟩⟩)).symm
  change m.right = (oldDesc T L B D hBD c).right
  exact congrArg (fun k : L.obj (expanded B D Q) ⟶ oldObject T L B c.pt => k.right) hh

end Colimit

/-- Every selected expanded piece is the actual lower colimit under the new root. -/
def isColimit (Q : LowerSet (Label B D)) : IsColimit (cocone T L B D Q) where
  desc c := desc T L B D hBD c
  fac c a := desc_fac T L B D hBD c a
  uniq c m hm := desc_uniq T L B D hBD c m hm

/-- All lower pieces of the original difference, retaining their whole chosen maps. -/
def lower : LowerSetColimitData (diagram T L B D) where
  cocone Q := cocone T L B D Q
  isColimit Q := isColimit T L B D hBD Q

/-- The entire selected lower-object function remains the original expanded-piece function. -/
theorem lower_obj_function :
    (fun Q => (lower T L B D hBD).obj Q) = (fun Q => obj T L B D Q) := rfl

/-- Original difference comparisons are the same selected expanded comparisons. -/
theorem lower_map {Q R : LowerSet (Label B D)} (h : Q ≤ R) :
    (lower T L B D hBD).map h = map T L B D h := by
  apply (lower T L B D hBD).hom_ext
  intro a
  rw [(lower T L B D hBD).ι_map]
  change map T L B D
      (show LowerSet.Iic a.1 ≤ R from fun b hb => R.lower hb (memOfLE h a.2)) =
    map T L B D (show LowerSet.Iic a.1 ≤ Q from fun b hb => Q.lower hb a.2) ≫
      map T L B D h
  exact (map_comp T L B D
    (show LowerSet.Iic a.1 ≤ Q from fun b hb => Q.lower hb a.2) h).symm

/-- The recorded strict-predecessor cocone uses exactly the selected expanded Iio piece. -/
abbrev predecessor (a : Label B D) :
    ColimitCocone (restriction (diagram T L B D) (LowerSet.Iio a)) :=
  ⟨cocone T L B D (LowerSet.Iio a), isColimit T L B D hBD (LowerSet.Iio a)⟩

/-- Its actual map to the vertex is the same original selected lower map. -/
theorem predecessorMap (a : Label B D) :
    cellTreePredecessorMap (diagram T L B D) a (predecessor T L B D hBD a) =
      map T L B D (show LowerSet.Iio a ≤ LowerSet.Iic a from fun _ hp => hp.le) := by
  apply (predecessor T L B D hBD a).isColimit.hom_ext
  intro b
  rw [cellTreePredecessorMap_fac]
  change map T L B D
      (show LowerSet.Iic b.1 ≤ LowerSet.Iic a from fun c hc => hc.trans b.2.le) =
    map T L B D
      (show LowerSet.Iic b.1 ≤ LowerSet.Iio a from fun c hc => lt_of_le_of_lt hc b.2) ≫
        map T L B D
          (show LowerSet.Iio a ≤ LowerSet.Iic a from fun _ hp => hp.le)
  exact (map_comp T L B D
    (show LowerSet.Iic b.1 ≤ LowerSet.Iio a from fun c hc => lt_of_le_of_lt hc b.2)
    (show LowerSet.Iio a ≤ LowerSet.Iic a from fun _ hp => hp.le)).symm

section Cells

/-- The actual selected strict-predecessor inclusion in the original diagram. -/
abbrev originalPredecessorInclusion (a : P) :
    L.obj (LowerSet.Iio a) ⟶ L.obj (LowerSet.Iic a) :=
  L.map (show LowerSet.Iio a ≤ LowerSet.Iic a from fun _ hp => hp.le)

/-- Both given colimit choices compare the same original predecessor map. -/
theorem originalPredecessorComparison (a : P) :
    (T.predecessorIso L a).hom ≫ T.predecessorMap a =
      originalPredecessorInclusion T L a ≫ (L.principalIso a).hom := by
  apply L.hom_ext
  intro b
  rw [← Category.assoc, T.ι_predecessorIso_hom, T.predecessorMap_fac,
    ← Category.assoc, L.ι_map, L.ι_principalIso_hom]

/-- The inverse comparisons retain the actual original map in both directions. -/
theorem originalPredecessorInverseComparison (a : P) :
    (T.predecessorMap a).right ≫ (L.principalIso a).inv.right =
      (T.predecessorIso L a).inv.right ≫ (originalPredecessorInclusion T L a).right := by
  apply (cancel_epi (T.predecessorIso L a).hom.right).1
  rw [← Category.assoc, ← Under.comp_right,
    originalPredecessorComparison T L a, Under.comp_right, Category.assoc,
    Under.hom_right_inv_right, Category.comp_id, ← Category.assoc,
    Under.hom_right_inv_right, Category.id_comp]

/-- The original cell on its same selected predecessor and principal colimit. -/
theorem originalSelectedIsPushout (a : P) :
    IsPushout
      (T.attaching a ≫ (T.predecessorIso L a).inv.right)
      (s (T.label a)).hom
      (originalPredecessorInclusion T L a).right
      (T.cell a ≫ (L.principalIso a).inv.right) := by
  refine (T.isPushout a).of_iso
    (Iso.refl _) ((Under.forget X).mapIso (T.predecessorIso L a).symm)
    (Iso.refl _) ((Under.forget X).mapIso (L.principalIso a).symm) ?_ ?_ ?_ ?_
  · simp only [Functor.mapIso_hom, Under.forget_map, Iso.symm_hom,
      Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · exact originalPredecessorInverseComparison T L a
  · simp only [Functor.mapIso_hom, Under.forget_map, Iso.symm_hom,
      Iso.refl_hom, Category.id_comp]

/-- The original intersections agree because the new cell label is outside B. -/
theorem intersection_Iio_Iic (a : Label B D) :
    B ⊓ LowerSet.Iio a.1 = B ⊓ LowerSet.Iic a.1 := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.1, hp.2.le⟩
  · intro hp
    refine ⟨hp.1, lt_of_le_of_ne hp.2 ?_⟩
    intro he
    exact a.2.2 (he ▸ hp.1)

/-- Gluing original lower unions gives the actual cobase square of this cell. -/
theorem successorUnionIsPushout (a : Label B D) :
    IsPushout
      (originalPredecessorInclusion T L a.1)
      (L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1))
      (L.map (le_sup_right : LowerSet.Iic a.1 ≤ B ⊔ LowerSet.Iic a.1))
      (L.map (sup_le_sup_left
        (show LowerSet.Iio a.1 ≤ LowerSet.Iic a.1 from fun _ hp => hp.le) B)) := by
  let hPred : LowerSet.Iio a.1 ≤ LowerSet.Iic a.1 := fun _ hp => hp.le
  let hStep : B ⊔ LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iic a.1 := sup_le_sup_left hPred B
  let hInter : B ⊓ LowerSet.Iic a.1 ≤ LowerSet.Iio a.1 := by
    intro p hp
    exact lt_of_le_of_ne hp.2 (fun he => a.2.2 (he ▸ hp.1))
  have square : originalPredecessorInclusion T L a.1 ≫
      L.map (le_sup_right : LowerSet.Iic a.1 ≤ B ⊔ LowerSet.Iic a.1) =
    L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1) ≫ L.map hStep := by
    dsimp only [originalPredecessorInclusion]
    rw [L.map_comp, L.map_comp]
  have agree (c : PushoutCocone (originalPredecessorInclusion T L a.1)
      (L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1))) :
      L.map (inf_le_left : B ⊓ LowerSet.Iic a.1 ≤ B) ≫
          (L.map (le_sup_left : B ≤ B ⊔ LowerSet.Iio a.1) ≫ c.inr) =
        L.map (inf_le_right : B ⊓ LowerSet.Iic a.1 ≤ LowerSet.Iic a.1) ≫ c.inl := by
    calc
      _ = (L.map hInter ≫
          L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1)) ≫ c.inr := by
        rw [← Category.assoc, L.map_comp, L.map_comp]
      _ = L.map hInter ≫ (originalPredecessorInclusion T L a.1 ≫ c.inl) := by
        rw [Category.assoc, c.condition]
      _ = _ := by
        dsimp only [originalPredecessorInclusion]
        rw [← Category.assoc, L.map_comp]
  let d (c : PushoutCocone (originalPredecessorInclusion T L a.1)
      (L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1))) :=
    L.unionDesc (L.map (le_sup_left : B ≤ B ⊔ LowerSet.Iio a.1) ≫ c.inr) c.inl (agree c)
  have left (c : PushoutCocone (originalPredecessorInclusion T L a.1)
      (L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1))) :
      L.map (le_sup_right : LowerSet.Iic a.1 ≤ B ⊔ LowerSet.Iic a.1) ≫ d c = c.inl :=
    L.map_right_unionDesc _ _ _
  have right (c : PushoutCocone (originalPredecessorInclusion T L a.1)
      (L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1))) :
      L.map hStep ≫ d c = c.inr := by
    apply (L.union_isPushout B (LowerSet.Iio a.1)).hom_ext
    · rw [← Category.assoc, L.map_comp]
      exact L.map_left_unionDesc _ _ _
    · rw [← Category.assoc, ← square, Category.assoc, left]
      exact c.condition
  refine ⟨⟨square⟩, ⟨PushoutCocone.IsColimit.mk square d left right ?_⟩⟩
  intro c m hLeft hRight
  apply (L.union_isPushout B (LowerSet.Iic a.1)).hom_ext
  · have hm : L.map (le_sup_left : B ≤ B ⊔ LowerSet.Iic a.1) ≫ m =
        L.map (le_sup_left : B ≤ B ⊔ LowerSet.Iio a.1) ≫ c.inr := by
      rw [← L.map_comp (le_sup_left : B ≤ B ⊔ LowerSet.Iio a.1) hStep,
        Category.assoc, hRight]
    exact hm.trans (L.map_left_unionDesc _ _ _).symm
  · exact hLeft.trans (left c).symm

/-- The actual selected original attaching map into the new predecessor object. -/
def attaching (a : Label B D) :
    (s (T.label a.1)).left ⟶ (predecessor T L B D hBD a).cocone.pt.right :=
  T.attaching a.1 ≫ (T.predecessorIso L a.1).inv.right ≫
    (L.map (show LowerSet.Iio a.1 ≤ expanded B D (LowerSet.Iio a) from by
      rw [expanded_Iio]
      exact le_sup_right)).right

/-- The actual original cell-target function into the expanded vertex. -/
def cell (a : Label B D) :
    (s (T.label a.1)).right ⟶ ((diagram T L B D).obj a).right :=
  T.cell a.1 ≫ (L.principalIso a.1).inv.right ≫
    (L.map (show LowerSet.Iic a.1 ≤ expanded B D (LowerSet.Iic a) from by
      rw [expanded_Iic]
      exact le_sup_right)).right

/-- Every difference occurrence is a pushout of the same original generator. -/
theorem isPushout (a : Label B D) :
    IsPushout (attaching T L B D hBD a) (s (T.label a.1)).hom
      (cellTreePredecessorMap (diagram T L B D) a (predecessor T L B D hBD a)).right
      (cell T L B D a) := by
  rw [predecessorMap]
  have hU := (successorUnionIsPushout T L B D a).map (Under.forget X)
  have hP := (originalSelectedIsPushout T L a.1).paste_horiz hU.flip
  let eP : L.obj (B ⊔ LowerSet.Iio a.1) ≅ L.obj (expanded B D (LowerSet.Iio a)) :=
    L.functor.mapIso (eqToIso (expanded_Iio B D a).symm)
  let eV : L.obj (B ⊔ LowerSet.Iic a.1) ≅ L.obj (expanded B D (LowerSet.Iic a)) :=
    L.functor.mapIso (eqToIso (expanded_Iic B D a).symm)
  have eP_hom : eP.hom = L.map (leOfHom (eqToHom (expanded_Iio B D a).symm)) := rfl
  have eV_hom : eV.hom = L.map (leOfHom (eqToHom (expanded_Iic B D a).symm)) := rfl
  refine hP.of_iso (Iso.refl _) ((Under.forget X).mapIso eP)
    (Iso.refl _) ((Under.forget X).mapIso eV) ?_ ?_ ?_ ?_
  · change ((T.attaching a.1 ≫ (T.predecessorIso L a.1).inv.right) ≫
        (L.map (le_sup_right : LowerSet.Iio a.1 ≤ B ⊔ LowerSet.Iio a.1)).right) ≫
        eP.hom.right = 𝟙 _ ≫ attaching T L B D hBD a
    rw [Category.id_comp, eP_hom]
    dsimp only [attaching]
    rw [Category.assoc, Category.assoc, ← Under.comp_right, L.map_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change (L.map (sup_le_sup_left
        (show LowerSet.Iio a.1 ≤ LowerSet.Iic a.1 from fun _ hp => hp.le) B)).right ≫
        eV.hom.right = eP.hom.right ≫
          (map T L B D (show LowerSet.Iio a ≤ LowerSet.Iic a from fun _ hp => hp.le)).right
    rw [eP_hom, eV_hom]
    dsimp only [map]
    simp only [Under.homMk_right]
    rw [← Under.comp_right, ← Under.comp_right, L.map_comp, L.map_comp]
  · change ((T.cell a.1 ≫ (L.principalIso a.1).inv.right) ≫
        (L.map (le_sup_right : LowerSet.Iic a.1 ≤ B ⊔ LowerSet.Iic a.1)).right) ≫
        eV.hom.right = 𝟙 _ ≫ cell T L B D a
    rw [Category.id_comp, eV_hom]
    dsimp only [cell]
    rw [Category.assoc, Category.assoc, ← Under.comp_right, L.map_comp]

end Cells

section Endpoint

/-- The endpoint comparison is induced by the actual equality of original label sets. -/
def endpointIso :
    obj T L B D ⊤ ≅ Under.mk ((L.map hBD).right) := by
  let e := L.functor.mapIso (eqToIso (expanded_top B D hBD))
  refine Under.isoMk ((Under.forget X).mapIso e) ?_
  change (L.map (base_le_expanded B D ⊤)).right ≫ e.hom.right = (L.map hBD).right
  have he : e.hom = L.map (leOfHom (eqToHom (expanded_top B D hBD))) := by
    rfl
  rw [he, ← Under.comp_right, L.map_comp]

/-- Extend the original full difference cocone to the literal selected D endpoint. -/
def endpointCocone : Cocone (diagram T L B D) :=
  (lower T L B D hBD).fullCocone.extend (endpointIso T L B D hBD).hom

/-- The same original endpoint cocone, with its whole universal property. -/
def endpoint : ColimitCocone (diagram T L B D) where
  cocone := endpointCocone T L B D hBD
  isColimit := IsColimit.ofIsoColimit
    (lower T L B D hBD).isColimitFullCocone
    (Cocone.ext (endpointIso T L B D hBD) (fun _ => rfl))

/-- Every endpoint vertex leg is its actual original expanded-label comparison. -/
theorem endpoint_leg (a : Label B D) :
    ((endpoint T L B D hBD).cocone.ι.app a).right =
      (L.map (show expanded B D (LowerSet.Iic a) ≤ D from
        expanded_le B D hBD (LowerSet.Iic a))).right := by
  change ((map T L B D (le_top : LowerSet.Iic a ≤ ⊤)).right ≫
    (endpointIso T L B D hBD).hom.right) = _
  dsimp only [map, endpointIso]
  simp only [Under.homMk_right, Under.isoMk_hom_right, Functor.mapIso_hom,
    Under.forget_map]
  rw [← Under.comp_right]
  change (L.map _ ≫ L.functor.map (eqToHom (expanded_top B D hBD))).right = _
  change (L.map _ ≫ L.map (leOfHom (eqToHom (expanded_top B D hBD)))).right = _
  rw [L.map_comp]

end Endpoint

/-- The complete actual difference tree on the literal original remaining labels. -/
def tree : CellTree s (L.obj B).right (P := Label B D) where
  wellFounded := InvImage.wf (fun a : Label B D => a.1) T.wellFounded
  diagram := diagram T L B D
  label a := T.label a.1
  predecessor a := predecessor T L B D hBD a
  attaching a := attaching T L B D hBD a
  cell a := cell T L B D a
  isPushout a := isPushout T L B D hBD a
  endpoint := endpoint T L B D hBD

/-- The endpoint is the original selected D object under the selected B root. -/
theorem tree_endpoint :
    (tree T L B D hBD).endpointObj = Under.mk ((L.map hBD).right) := rfl

/-- The relative tree represents the exact same original lower inclusion. -/
theorem tree_hom : (tree T L B D hBD).hom = (L.map hBD).right := rfl

/-- The original generator-label function is unchanged on the entire difference carrier. -/
theorem tree_label_function :
    (tree T L B D hBD).label = (fun a : Label B D => T.label a.1) := rfl

/-- The full vertex function is the same selected original union-of-labels function. -/
theorem tree_vertex_function :
    (fun a : Label B D => (tree T L B D hBD).vertex a) =
      (fun a : Label B D => obj T L B D (LowerSet.Iic a)) := rfl

/-- The full predecessor function retains every actual expanded strict-lower colimit. -/
theorem tree_predecessor_function :
    (fun a : Label B D => (tree T L B D hBD).predecessor a) =
      (fun a : Label B D => predecessor T L B D hBD a) := rfl

/-- All actual lower colimits remain available on this same whole difference tree. -/
abbrev treeLower : LowerSetColimitData (tree T L B D hBD).diagram := lower T L B D hBD

/-- Goodness uses the actual inherited predecessor injection and original generators. -/
theorem tree_good (chi : Cardinal.{w}) [Fact chi.IsRegular] (good : T.IsGood chi) :
    (tree T L B D hBD).IsGood chi where
  presentable_source a := good.presentable_source a.1
  presentable_target a := good.presentable_target a.1
  predecessor_lt a := (good.predecessor_lt a.1).of_injective
    (fun b : Set.Iio a => (⟨b.1.1, b.2⟩ : Set.Iio a.1))
    (by
      intro b c h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Set.Iio a.1 => z.1) h)

end CategoryTheory.SmallObject.CellTreeIncrement
