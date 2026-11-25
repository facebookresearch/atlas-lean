/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ProperFaceBoundary
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatching

/-!
# Whole boundary maps and actual simplicial matching objects

The proper-face boundary colimit represents the matching object of a
simplicial set. The comparison identifies each matching projection with
restriction along the corresponding proper-face inclusion.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.BoundaryMatching
open SSet.ProperFaceBoundary

/-- Whole original boundary maps give the actual cone of all proper-face simplices. -/
def boundaryCone (X : SSet.{u}) (n : ℕ) : Cone (SimplicialObject.matchingDiagram X n) where
  pt := ((boundary.{u} n : SSet.{u}) ⟶ X)
  π :=
    { app := fun a => ↾fun f => yonedaEquiv (properFaceBoundaryInclusion a ≫ f)
      naturality := by
        intro a b g
        ext f
        change yonedaEquiv (properFaceBoundaryInclusion b ≫ f) =
          X.map g.hom.right (yonedaEquiv (properFaceBoundaryInclusion a ≫ f))
        have h := yonedaEquiv_naturality (X := X) g.hom.right.unop
          (properFaceBoundaryInclusion.{u} a ≫ f)
        have hg : stdSimplex.map g.hom.right.unop ≫
            (properFaceBoundaryInclusion.{u} a ≫ f) = properFaceBoundaryInclusion b ≫ f :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ f) (properFaceBoundaryInclusion_naturality g))
        exact (congrArg (fun z => yonedaEquiv (X := X) z) hg).symm.trans h.symm }

private def sections (X : SSet.{u}) (n : ℕ)
    (s : Cone (SimplicialObject.matchingDiagram X n)) (t : s.pt)
    (a : SimplicialObject.matchingIndex n) : stdSimplex.obj a.obj.right.unop ⟶ X :=
  (yonedaEquiv (X := X) (n := a.obj.right.unop)).symm (s.π.app a t)

private theorem sections_compatible (X : SSet.{u}) (n : ℕ)
    (s : Cone (SimplicialObject.matchingDiagram X n)) (t : s.pt)
    {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b) :
    stdSimplex.map g.hom.right.unop ≫ sections X n s t a = sections X n s t b := by
  have h := yonedaEquiv_symm_naturality_left (X := X) g.hom.right.unop
    (s.π.app a t : X.obj a.obj.right)
  exact h.trans (congrArg (fun z : X.obj b.obj.right =>
    (yonedaEquiv (X := X) (n := b.obj.right.unop)).symm z)
      (ConcreteCategory.congr_hom (s.w g) t))

private def descended (X : SSet.{u}) (n : ℕ)
    (s : Cone (SimplicialObject.matchingDiagram X n)) (t : s.pt) :
    (boundary.{u} n : SSet.{u}) ⟶ X :=
  Classical.choose (properFaceBoundary_sections n X (sections X n s t)
    (sections_compatible X n s t))

private theorem descended_face (X : SSet.{u}) (n : ℕ)
    (s : Cone (SimplicialObject.matchingDiagram X n)) (t : s.pt)
    (a : SimplicialObject.matchingIndex n) :
    properFaceBoundaryInclusion a ≫ descended X n s t = sections X n s t a :=
  (Classical.choose_spec (properFaceBoundary_sections n X (sections X n s t)
    (sections_compatible X n s t))).1 a

/-- The cone of boundary maps is a limit of the full matching diagram. -/
@[no_expose]
def boundaryConeIsLimit (X : SSet.{u}) (n : ℕ) : IsLimit (boundaryCone X n) where
  lift s := ↾fun t => descended X n s t
  fac s a := by
    ext t
    change yonedaEquiv (properFaceBoundaryInclusion a ≫ descended X n s t) = s.π.app a t
    rw [descended_face]
    exact yonedaEquiv.apply_symm_apply _
  uniq s m hm := by
    ext t
    apply (Classical.choose_spec (properFaceBoundary_sections n X (sections X n s t)
      (sections_compatible X n s t))).2
    intro a
    apply (yonedaEquiv (X := X) (n := a.obj.right.unop)).injective
    exact (ConcreteCategory.congr_hom (hm a) t).trans
      ((yonedaEquiv (X := X) (n := a.obj.right.unop)).apply_symm_apply _).symm

/-- The matching object is isomorphic to boundary maps without a fibrancy assumption. -/
def matchingBoundaryIso (X : SSet.{u}) (n : ℕ) :
    SimplicialObject.matchingObject X n ≅ ((boundary.{u} n : SSet.{u}) ⟶ X) :=
  (limit.isLimit (SimplicialObject.matchingDiagram X n)).conePointUniqueUpToIso
    (boundaryConeIsLimit X n)

/-- The inverse comparison retains every original proper-face evaluation. -/
theorem matchingBoundaryIso_inv_π (X : SSet.{u}) (n : ℕ)
    (a : SimplicialObject.matchingIndex n) :
    (matchingBoundaryIso X n).inv ≫ SimplicialObject.matchingπ X n a =
      (boundaryCone X n).π.app a :=
  (limit.isLimit (SimplicialObject.matchingDiagram X n)).conePointUniqueUpToIso_inv_comp
    (boundaryConeIsLimit X n) a

/-- The forward comparison preserves each actual matching projection as its same boundary face. -/
theorem matchingBoundaryIso_hom_π (X : SSet.{u}) (n : ℕ)
    (a : SimplicialObject.matchingIndex n) :
    (matchingBoundaryIso X n).hom ≫ (boundaryCone X n).π.app a =
      SimplicialObject.matchingπ X n a := by
  apply (cancel_epi (matchingBoundaryIso X n).inv).mp
  exact (Category.assoc (matchingBoundaryIso X n).inv (matchingBoundaryIso X n).hom
    ((boundaryCone X n).π.app a)).symm.trans
      ((congrArg (fun f => f ≫ (boundaryCone X n).π.app a)
        (matchingBoundaryIso X n).inv_hom_id).trans
          ((Category.id_comp _).trans (matchingBoundaryIso_inv_π X n a).symm))

/-- The same whole boundary map is recovered by evaluating every original matching projection. -/
theorem matchingBoundaryIso_hom_face (X : SSet.{u}) (n : ℕ)
    (b : SimplicialObject.matchingObject X n) (a : SimplicialObject.matchingIndex n) :
    properFaceBoundaryInclusion a ≫ (matchingBoundaryIso X n).hom b =
      yonedaEquiv.symm (SimplicialObject.matchingπ X n a b) := by
  apply (yonedaEquiv (X := X) (n := a.obj.right.unop)).injective
  have h := ConcreteCategory.congr_hom (matchingBoundaryIso_hom_π X n a) b
  exact h.trans ((yonedaEquiv (X := X) (n := a.obj.right.unop)).apply_symm_apply _).symm

/-- An actual simplex maps to its original boundary restriction under the matching comparison. -/
theorem matchingMap_readback (X : SSet.{u}) (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (matchingBoundaryIso X n).hom (SimplicialObject.matchingMap X n x) =
      (boundary.{u} n).ι ≫ yonedaEquiv.symm x := by
  apply (properFaceBoundaryIsColimit.{u} n).hom_ext
  intro a
  change properFaceBoundaryInclusion.{u} a.unop ≫
      (matchingBoundaryIso X n).hom (SimplicialObject.matchingMap X n x) =
    properFaceBoundaryInclusion.{u} a.unop ≫ ((boundary.{u} n).ι ≫ yonedaEquiv.symm x)
  rw [matchingBoundaryIso_hom_face, ← Category.assoc, properFaceBoundaryInclusion_ι,
    yonedaEquiv_symm_naturality_left]
  apply congrArg yonedaEquiv.symm
  exact ConcreteCategory.congr_hom (SimplicialObject.matchingMap_π X n a.unop) x

end SSet.BoundaryMatching
