/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionColimits

/-!
# Restricted original one-cell extension colimits

The actual old lower-colimit universal property and a genuine cell pushout construct the full
universal property on the old lower carrier together with its new cell.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.GoodCellExtensionOrder
open CategoryTheory.SmallObject.GoodCellExtensionDiagram
open CategoryTheory.SmallObject.GoodCellExtensionColimits
open CategoryTheory.SmallObject.LowerSetColimits

universe w t u v

namespace CategoryTheory.SmallObject.OriginalGoodification.RestrictedCellExtension

noncomputable section

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {Q : Type w} [PartialOrder Q] {A : Type t} {s : A → Arrow C} {X : C}
  (G : CellTree s X (P := Q)) (L : LowerSetColimitData G.diagram)
  (S E : LowerSet Q) (hSE : S ≤ E) (i : A)
  (a : (s i).left ⟶ (L.obj S).right)

/-- The literal restricted extension carrier contains precisely E and its one new cell. -/
abbrev extendedLower : letI := extensionOrder S; LowerSet (Index Q) := by
  letI := extensionOrder S
  exact {
    carrier := {x | match x.val with | some q => q ∈ E | none => True}
    lower' := by
      rintro ⟨y⟩ ⟨x⟩ h hy
      cases x with
      | none =>
        cases y with
        | none => trivial
        | some y => exact False.elim h
      | some x =>
        cases y with
        | none => exact hSE h
        | some y => exact E.lower' h hy }

/-- The original old diagram remains the restriction of G to E. -/
def oldRestrictionCocone
    (d : letI := extensionOrder S
      Cocone (restriction (diagram G L S i a) (extendedLower S E hSE))) :
    Cocone (restriction G.diagram E) := by
  letI := extensionOrder S
  exact {
    pt := d.pt
    ι := {
      app p := d.ι.app ⟨Index.old p.1, p.2⟩
      naturality p q h := by
        change G.diagram.map (homOfLE (leOfHom h)) ≫
          d.ι.app ⟨Index.old q.1, q.2⟩ =
            d.ι.app ⟨Index.old p.1, p.2⟩ ≫ 𝟙 _
        exact d.ι.naturality
          (homOfLE (leOfHom h) :
            (⟨Index.old p.1, p.2⟩ : extendedLower S E hSE) ⟶
              ⟨Index.old q.1, q.2⟩) } }

/-- The original old lower-colimit descender retains the entire restricted old cofan. -/
def restrictedOldDesc
    (d : letI := extensionOrder S
      Cocone (restriction (diagram G L S i a) (extendedLower S E hSE))) :
    letI := extensionOrder S
    L.obj E ⟶ d.pt := by
  letI := extensionOrder S
  exact (L.isColimit E).desc (oldRestrictionCocone G L S E hSE i a d)

/-- Every original old vertex leg factors through the actual old lower-colimit descender. -/
theorem restrictedOldDesc_fac
    (d : letI := extensionOrder S
      Cocone (restriction (diagram G L S i a) (extendedLower S E hSE))) (p : E) :
    letI := extensionOrder S
    L.ι E p ≫ restrictedOldDesc G L S E hSE i a d =
      d.ι.app ⟨Index.old p.1, p.2⟩ := by
  let _ := extensionOrder S
  exact (L.isColimit E).fac (oldRestrictionCocone G L S E hSE i a d) p

/-- The actual old support descender and new-cell leg agree on the original support. -/
theorem restrictedCompatibility
    (d : letI := extensionOrder S
      Cocone (restriction (diagram G L S i a) (extendedLower S E hSE))) :
    letI := extensionOrder S
    L.map hSE ≫ restrictedOldDesc G L S E hSE i a d =
      newStep G L S i a ≫ d.ι.app ⟨Index.new, by trivial⟩ := by
  let _ := extensionOrder S
  apply (L.isColimit S).hom_ext
  intro p
  rw [← Category.assoc, L.ι_map, restrictedOldDesc_fac]
  have hd := d.w (homOfLE p.2 :
    (⟨Index.old p.1, hSE p.2⟩ : extendedLower S E hSE) ⟶
      ⟨Index.new, by trivial⟩)
  change (L.ι S p ≫ newStep G L S i a) ≫ d.ι.app ⟨Index.new, by trivial⟩ =
    d.ι.app ⟨Index.old p.1, hSE p.2⟩ at hd
  exact hd.symm.trans (Category.assoc _ _ _)

/-- The actual original old-lower UP and a genuine cell pushout construct the restricted UP. -/
def restrictedExtensionIsColimit
    (d : letI := extensionOrder S
      Cocone (restriction (diagram G L S i a) (extendedLower S E hSE)))
    (k : letI := extensionOrder S; L.obj E ⟶ d.pt)
    (c : letI := extensionOrder S; (s i).right ⟶ d.pt.right)
    (sq : letI := extensionOrder S
      IsPushout (a ≫ (L.map hSE).right) (s i).hom k.right c)
    (hOld : ∀ p : E, letI := extensionOrder S
      L.ι E p ≫ k = d.ι.app ⟨Index.old p.1, p.2⟩)
    (hCell : letI := extensionOrder S
      newCell G L S i a ≫ (d.ι.app ⟨Index.new, by trivial⟩).right = c) :
    letI := extensionOrder S
    IsColimit d := by
  letI := extensionOrder S
  have hOldDesc : restrictedOldDesc G L S E hSE i a d = k := by
    apply (L.isColimit E).hom_ext
    intro p
    exact (restrictedOldDesc_fac G L S E hSE i a d p).trans (hOld p).symm
  let desc (e : Cocone (restriction (diagram G L S i a) (extendedLower S E hSE))) :
      d.pt ⟶ e.pt :=
    Under.homMk
      (sq.desc (restrictedOldDesc G L S E hSE i a e).right
        (newCell G L S i a ≫ (e.ι.app ⟨Index.new, by trivial⟩).right) (by
          have h := congrArg Under.Hom.right (restrictedCompatibility G L S E hSE i a e)
          change (L.map hSE).right ≫ (restrictedOldDesc G L S E hSE i a e).right =
            (newStep G L S i a).right ≫ (e.ι.app ⟨Index.new, by trivial⟩).right at h
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun k => a ≫ k) h).trans
              (((Category.assoc _ _ _).symm.trans
                (congrArg (fun k => k ≫ (e.ι.app ⟨Index.new, by trivial⟩).right)
                  (newPoint_isPushout G L S i a).w)).trans (Category.assoc _ _ _)))))
      (by
        rw [← Under.w k, Category.assoc, sq.inl_desc]
        exact Under.w (restrictedOldDesc G L S E hSE i a e))
  have hStep (e : Cocone (restriction (diagram G L S i a) (extendedLower S E hSE))) :
      k ≫ desc e = restrictedOldDesc G L S E hSE i a e := by
    apply Under.UnderMorphism.ext
    exact sq.inl_desc _ _ _
  have hNew (e : Cocone (restriction (diagram G L S i a) (extendedLower S E hSE))) :
      d.ι.app ⟨Index.new, by trivial⟩ ≫ desc e = e.ι.app ⟨Index.new, by trivial⟩ := by
    apply newPoint_hom_ext G L S i a
    · calc
        newStep G L S i a ≫
            (d.ι.app ⟨Index.new, by trivial⟩ ≫ desc e) =
          (newStep G L S i a ≫ d.ι.app ⟨Index.new, by trivial⟩) ≫ desc e :=
            (Category.assoc _ _ _).symm
        _ = (L.map hSE ≫ restrictedOldDesc G L S E hSE i a d) ≫ desc e :=
          congrArg (fun k => k ≫ desc e) (restrictedCompatibility G L S E hSE i a d).symm
        _ = L.map hSE ≫ (k ≫ desc e) := by rw [hOldDesc, Category.assoc]
        _ = L.map hSE ≫ restrictedOldDesc G L S E hSE i a e :=
          congrArg (fun k => L.map hSE ≫ k) (hStep e)
        _ = newStep G L S i a ≫ e.ι.app ⟨Index.new, by trivial⟩ :=
          restrictedCompatibility G L S E hSE i a e
    · change newCell G L S i a ≫
        ((d.ι.app ⟨Index.new, by trivial⟩).right ≫ (desc e).right) = _
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ (desc e).right) hCell)).trans (sq.inr_desc _ _ _)
  refine {
    desc := desc
    fac := ?_
    uniq := ?_ }
  · intro e p
    rcases p with ⟨⟨p⟩, hp⟩
    cases p with
    | none => exact hNew e
    | some p =>
      exact (congrArg (fun k => k ≫ desc e) (hOld ⟨p, hp⟩).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => L.ι E ⟨p, hp⟩ ≫ k) (hStep e)).trans
            (restrictedOldDesc_fac G L S E hSE i a e ⟨p, hp⟩)))
  · intro e m hm
    have hk : k ≫ m = restrictedOldDesc G L S E hSE i a e := by
      apply (L.isColimit E).hom_ext
      intro p
      rw [← Category.assoc, hOld]
      exact (hm ⟨Index.old p.1, p.2⟩).trans
        (restrictedOldDesc_fac G L S E hSE i a e p).symm
    apply Under.UnderMorphism.ext
    apply sq.hom_ext
    · exact congrArg Under.Hom.right (hk.trans (hStep e).symm)
    · have h := congrArg (fun f => newCell G L S i a ≫ f.right)
        (hm ⟨Index.new, by trivial⟩)
      change newCell G L S i a ≫
        ((d.ι.app ⟨Index.new, by trivial⟩).right ≫ m.right) = _ at h
      have h' : c ≫ m.right =
          newCell G L S i a ≫ (e.ι.app ⟨Index.new, by trivial⟩).right :=
        (congrArg (fun k => k ≫ m.right) hCell.symm).trans
          ((Category.assoc _ _ _).trans h)
      exact h'.trans (sq.inr_desc _ _ _).symm

end

end CategoryTheory.SmallObject.OriginalGoodification.RestrictedCellExtension
