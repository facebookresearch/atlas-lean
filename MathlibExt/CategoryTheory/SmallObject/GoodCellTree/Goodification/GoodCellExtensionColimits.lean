/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionDiagram

/-!
# The actual whole colimit of the one-cell good-order extension

The original old endpoint colimit and the two actual pushout squares give
the complete new endpoint universal property. All lower-cofan comparisons,
old vertex legs, new cell legs and original root equations are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.GoodCellExtensionColimits

open Limits LowerSetColimits GoodCellExtensionOrder GoodCellExtensionDiagram

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {P : Type w} [PartialOrder P] {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B : LowerSet P) (i : A) (a : (s i).left ⟶ (L.obj B).right)
  (d : letI := extensionOrder B
    Cocone (diagram T L B i a))

/-- The actual original old-vertex leg of the complete extension cocone. -/
abbrev oldLeg (p : P) : letI := extensionOrder B
    T.vertex p ⟶ d.pt := by
  letI := extensionOrder B
  exact d.ι.app (Index.old p)

/-- The actual new-vertex leg of the same complete extension cocone. -/
abbrev newLeg : letI := extensionOrder B
    newPoint T L B i a ⟶ d.pt := by
  letI := extensionOrder B
  exact d.ι.app Index.new

/-- The old original diagram keeps its complete actual cocone. -/
def oldCocone : Cocone T.diagram := by
  letI := extensionOrder B
  exact {
    pt := d.pt
    ι := {
      app := oldLeg T L B i a d
      naturality p q h := by
        let h' : Index.old p ⟶ Index.old q := homOfLE (leOfHom h)
        have hd := d.w h'
        change T.diagram.map h ≫ oldLeg T L B i a d q =
          oldLeg T L B i a d p at hd
        exact hd.trans (Category.comp_id _).symm } }

/-- The actual old endpoint descender uses its original entire colimit UP. -/
def oldDesc : letI := extensionOrder B
    T.endpointObj ⟶ d.pt := by
  letI := extensionOrder B
  exact T.endpoint.isColimit.desc (oldCocone T L B i a d)

/-- Every original old vertex leg retains its actual descender factor equation. -/
@[reassoc]
theorem oldDesc_fac (p : P) :
    letI := extensionOrder B
    T.inclusion p ≫ oldDesc T L B i a d = oldLeg T L B i a d p := by
  let : PartialOrder (Index P) := extensionOrder B
  exact T.endpoint.isColimit.fac (oldCocone T L B i a d) p

/-- The original lower-colimit UP detects the complete old/new cocone compatibility. -/
theorem lowerCompatibility :
    letI := extensionOrder B
    lowerToEndpoint T L B ≫ oldDesc T L B i a d =
      newStep T L B i a ≫ newLeg T L B i a d := by
  let : PartialOrder (Index P) := extensionOrder B
  apply (L.isColimit B).hom_ext
  intro b
  change L.ι B b ≫ (lowerToEndpoint T L B ≫ oldDesc T L B i a d) =
    L.ι B b ≫ (newStep T L B i a ≫ newLeg T L B i a d)
  rw [← Category.assoc, lowerToEndpoint_fac, oldDesc_fac, ← Category.assoc]
  let h : Index.old b.1 ⟶ Index.new := homOfLE b.2
  exact (d.w h).symm

/-- The original global attaching map commutes with the actual new cell image. -/
theorem descSquare :
    letI := extensionOrder B
    globalAttaching T L B i a ≫ (oldDesc T L B i a d).right =
      (s i).hom ≫ (newCell T L B i a ≫ (newLeg T L B i a d).right) := by
  let : PartialOrder (Index P) := extensionOrder B
  have h := congrArg Under.Hom.right (lowerCompatibility T L B i a d)
  change (lowerToEndpoint T L B).right ≫ (oldDesc T L B i a d).right =
    (newStep T L B i a).right ≫ (newLeg T L B i a d).right at h
  change (a ≫ (lowerToEndpoint T L B).right) ≫ (oldDesc T L B i a d).right = _
  rw [Category.assoc, h, ← Category.assoc, (newPoint_isPushout T L B i a).w,
    Category.assoc]

/-- The whole endpoint descender is the actual original global pushout descender under its root. -/
def wholeDesc : letI := extensionOrder B
    wholePoint T L B i a ⟶ d.pt := by
  letI := extensionOrder B
  exact Under.homMk
    (pushout.desc (oldDesc T L B i a d).right
      (newCell T L B i a ≫ (newLeg T L B i a d).right) (descSquare T L B i a d))
    (by
      change (T.hom ≫ pushout.inl (globalAttaching T L B i a) (s i).hom) ≫ _ = d.pt.hom
      rw [Category.assoc, pushout.inl_desc]
      exact Under.w (oldDesc T L B i a d))

/-- The actual old endpoint inclusion keeps its full universal factor equation. -/
theorem wholeDesc_step :
    letI := extensionOrder B
    endpointStep T L B i a ≫ wholeDesc T L B i a d = oldDesc T L B i a d := by
  let : PartialOrder (Index P) := extensionOrder B
  apply Under.UnderMorphism.ext
  exact pushout.inl_desc _ _ _

/-- The original whole cell-target map has the actual new-vertex factor equation. -/
@[reassoc]
theorem wholeDesc_cell :
    letI := extensionOrder B
    wholeCell T L B i a ≫ (wholeDesc T L B i a d).right =
      newCell T L B i a ≫ (newLeg T L B i a d).right := by
  let : PartialOrder (Index P) := extensionOrder B
  exact pushout.inr_desc _ _ _

/-- Both original local pushout maps determine each full new-vertex morphism. -/
theorem newPoint_hom_ext {U : Under X} {f g : newPoint T L B i a ⟶ U}
    (hLower : newStep T L B i a ≫ f = newStep T L B i a ≫ g)
    (hCell : newCell T L B i a ≫ f.right = newCell T L B i a ≫ g.right) : f = g := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · exact congrArg Under.Hom.right hLower
  · exact hCell

/-- The actual new-vertex endpoint leg retains its complete universal factor equation. -/
theorem wholeDesc_new :
    letI := extensionOrder B
    newToWhole T L B i a ≫ wholeDesc T L B i a d = newLeg T L B i a d := by
  let : PartialOrder (Index P) := extensionOrder B
  apply newPoint_hom_ext T L B i a
  · rw [← Category.assoc, newToWhole_step, Category.assoc, wholeDesc_step,
      lowerCompatibility]
  · change newCell T L B i a ≫
      ((newToWhole T L B i a).right ≫ (wholeDesc T L B i a d).right) = _
    rw [← Category.assoc, newToWhole_cell, wholeDesc_cell]

/-- Every complete actual original endpoint cocone leg factors through the same whole descender. -/
theorem wholeDesc_fac (x : Index P) :
    letI := extensionOrder B
    endpointLeg T L B i a x ≫ wholeDesc T L B i a d = d.ι.app x := by
  let : PartialOrder (Index P) := extensionOrder B
  rcases x with ⟨x⟩
  cases x with
  | none => exact wholeDesc_new T L B i a d
  | some p =>
    change (T.inclusion p ≫ endpointStep T L B i a) ≫ wholeDesc T L B i a d =
      oldLeg T L B i a d p
    rw [Category.assoc, wholeDesc_step, oldDesc_fac]

/-- The original old colimit and actual whole cell map uniquely detect the whole descender. -/
theorem wholeDesc_uniq : letI := extensionOrder B
    ∀ (m : wholePoint T L B i a ⟶ d.pt)
      (_ : ∀ x : Index P, endpointLeg T L B i a x ≫ m = d.ι.app x),
      m = wholeDesc T L B i a d := by
  let : PartialOrder (Index P) := extensionOrder B
  intro m hm
  have hOld : endpointStep T L B i a ≫ m = oldDesc T L B i a d := by
    apply T.endpoint.isColimit.hom_ext
    intro p
    change T.inclusion p ≫ (endpointStep T L B i a ≫ m) =
      T.inclusion p ≫ oldDesc T L B i a d
    rw [oldDesc_fac, ← Category.assoc]
    exact hm (Index.old p)
  have hNew : newToWhole T L B i a ≫ m = newLeg T L B i a d := hm Index.new
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · exact congrArg Under.Hom.right (hOld.trans (wholeDesc_step T L B i a d).symm)
  · have h := congrArg (fun f => newCell T L B i a ≫ f.right) hNew
    change newCell T L B i a ≫ ((newToWhole T L B i a).right ≫ m.right) =
      newCell T L B i a ≫ (newLeg T L B i a d).right at h
    rw [← Category.assoc, newToWhole_cell] at h
    exact h.trans (wholeDesc_cell T L B i a d).symm

/-- The entire constructed endpoint cocone has its actual original whole colimit UP. -/
def wholeEndpointIsColimit : letI := extensionOrder B
    IsColimit (endpointCocone T L B i a) := by
  letI := extensionOrder B
  exact {
    desc := wholeDesc T L B i a
    fac := wholeDesc_fac T L B i a
    uniq := wholeDesc_uniq T L B i a }

end CategoryTheory.SmallObject.GoodCellExtensionColimits
