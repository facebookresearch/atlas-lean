/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Fubini

/-!
# Entire actual pointwise Group cocone comparison and its genuine Fubini word

Every original cocone of whole Nat group diagrams gives actual inner
quotient descents, natural on the second index. The SAME actual Group
functor maps the full cocone and constructs its outer descent. All pair
legs prove that this entire descent is precisely the genuine Fubini hom
followed by the actual pointwise-colimit map. Full source-matrix and
target-cocone naturalities retain every original input map. A genuinely
proved pointwise Iso therefore gives both actual comparison functions.
No pointwise telescope Iso, native compactness or stable law is data
here; native callers still must prove the original complete components.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v uC vC
open CategoryTheory CategoryTheory.Limits

private theorem originalPointwiseLegSquare
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (x : A ⟶ F) (y : F ⟶ D) (z : F ⟶ E)
    (u : B ⟶ G) (v : G ⟶ E) (w : A ⟶ G)
    (hMap : a ≫ b = x ≫ y) (hDesc : y ≫ c = z)
    (hNatural : x ≫ z = w ≫ v) (hFac : a ≫ u = w) :
    a ≫ (b ≫ c) = a ≫ (u ≫ v) := by
  rw [← Category.assoc, hMap, Category.assoc, hDesc, hNatural,
    ← Category.assoc a u v, hFac]

private theorem originalCompositeLegJoining
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (s : A ⟶ F) (t : F ⟶ D) (u : F ⟶ G) (v : G ⟶ E) (w : A ⟶ G)
    (hFirst : a ≫ b = s ≫ t) (hSecond : t ≫ c = u ≫ v) (hThird : s ≫ u = w) :
    a ≫ (b ≫ c) = w ≫ v := by
  rw [← Category.assoc, hFirst, Category.assoc, hSecond,
    ← Category.assoc s u v, hThird]

namespace GrpCat.FilteredColimits.PointwiseComparison
open GrpCat.FilteredColimits.Fubini

/-- The actual full diagram cocone evaluates at the same original second index. -/
def evaluatedCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) (n : ℕ) :
    Cocone (F.flip.obj n) where
  pt := c.pt.obj n
  ι :=
    { app := fun i => (c.ι.app i).app n
      naturality := fun {i i'} f => by
        have h : (F.map f).app n ≫ (c.ι.app i').app n = (c.ι.app i).app n :=
          congr_app (c.w f) n
        exact h.trans (Category.comp_id _).symm }

/-- Genuine original inner UPL gives the full actual pointwise descent. -/
def pointwiseDesc (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) (n : ℕ) :
    GrpCat.FilteredColimits.colimit (F.flip.obj n) ⟶ c.pt.obj n :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.flip.obj n)).desc
    (evaluatedCocone F c n)

/-- EVERY actual original inner quotient leg preserves the complete original cocone component. -/
theorem pointwiseDesc_fac (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) (n i : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (F.flip.obj n)).ι.app i ≫ pointwiseDesc F c n =
      (c.ι.app i).app n :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.flip.obj n)).fac
    (evaluatedCocone F c n) i

/-- The ENTIRE actual pointwise descent is natural on all original second-index maps. -/
def pointwiseComparison (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) :
    F.flip ⋙ natQuotientColimit ⟶ c.pt where
  app := pointwiseDesc F c
  naturality {n m} f := by
    apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.flip.obj n)).hom_ext
    intro i
    have hMap := (colimitCoconeIsColimit (F.flip.obj n)).ι_map
      (colimitCocone (F.flip.obj m)) (F.flip.map f) i
    have hDesc := pointwiseDesc_fac F c m i
    have hNatural := (c.ι.app i).naturality f
    have hFac := pointwiseDesc_fac F c n i
    exact originalPointwiseLegSquare
      ((GrpCat.FilteredColimits.colimitCocone (F.flip.obj n)).ι.app i)
      (natQuotientColimit.map (F.flip.map f)) (pointwiseDesc F c m)
      ((F.obj i).map f) ((GrpCat.FilteredColimits.colimitCocone (F.flip.obj m)).ι.app i)
      ((c.ι.app i).app m) (pointwiseDesc F c n) (c.pt.map f) ((c.ι.app i).app n)
      hMap hDesc hNatural hFac

/-- The full actual outer cocone is the SAME genuine Group functor applied to the whole cocone. -/
def mappedGroupCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) :
    Cocone (innerColimitDiagram F) :=
  natQuotientColimit.mapCocone c

/-- Genuine original outer UPL constructs the actual whole cocone comparison map. -/
def groupCoconeComparisonDesc (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) :
    iteratedColimitFunctor.obj F ⟶ GrpCat.FilteredColimits.colimit c.pt :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (innerColimitDiagram F)).desc
    (mappedGroupCocone F c)

/-- EVERY complete original outer quotient leg retains the actual Group image of its cocone leg. -/
theorem groupCoconeComparisonDesc_fac (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) (i : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i ≫
        groupCoconeComparisonDesc F c = natQuotientColimit.map (c.ι.app i) :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (innerColimitDiagram F)).fac
    (mappedGroupCocone F c) i

/-- ALL actual original pair legs preserve the original outer descent's complete function. -/
theorem groupCoconeComparisonDesc_joint_fac
    (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) (i j : ℕ) :
    jointLeg F i j ≫ groupCoconeComparisonDesc F c =
      (c.ι.app i).app j ≫ (GrpCat.FilteredColimits.colimitCocone c.pt).ι.app j := by
  have hOuter := groupCoconeComparisonDesc_fac F c i
  have hInner := (colimitCoconeIsColimit (F.obj i)).ι_map (colimitCocone c.pt) (c.ι.app i) j
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j ≫ f)
      hOuter).trans hInner)

/-- ALL original pair legs identify the actual Fubini/pointwise map's complete function. -/
theorem fubini_pointwise_joint_fac (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) (i j : ℕ) :
    jointLeg F i j ≫ ((fubiniIso F).hom ≫
        natQuotientColimit.map (pointwiseComparison F c)) =
      (c.ι.app i).app j ≫ (GrpCat.FilteredColimits.colimitCocone c.pt).ι.app j := by
  have hFirst := fubiniIso_hom_leg F i j
  have hSecond := (colimitCoconeIsColimit (innerColimitDiagram F.flip)).ι_map
    (colimitCocone c.pt) (pointwiseComparison F c) j
  have hThird := pointwiseDesc_fac F c j i
  exact originalCompositeLegJoining (jointLeg F i j) ((fubiniIso F).hom)
    (natQuotientColimit.map (pointwiseComparison F c))
    ((GrpCat.FilteredColimits.colimitCocone (F.flip.obj j)).ι.app i)
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F.flip)).ι.app j)
    (pointwiseDesc F c j) ((GrpCat.FilteredColimits.colimitCocone c.pt).ι.app j)
    ((c.ι.app i).app j) hFirst hSecond hThird

/-- Genuine pair UPL proves the ENTIRE original outer comparison equals its actual Fubini word. -/
theorem groupCoconeComparisonDesc_fubini_word (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F) :
    groupCoconeComparisonDesc F c = (fubiniIso F).hom ≫
      natQuotientColimit.map (pointwiseComparison F c) := by
  apply (jointCoconeIsColimit F).hom_ext
  rintro ⟨i, j⟩
  exact (groupCoconeComparisonDesc_joint_fac F c i j).trans
    (fubini_pointwise_joint_fac F c i j).symm

/-- A proved actual whole pointwise Iso gives BOTH original cocone comparison Iso functions. -/
def groupCoconeComparisonIso (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F)
    (e : F.flip ⋙ natQuotientColimit ≅ c.pt) :
    iteratedColimitFunctor.obj F ≅ GrpCat.FilteredColimits.colimit c.pt :=
  fubiniIso F ≪≫ natQuotientColimit.mapIso e

/-- The actual original comparison Iso hom is the whole UPL descent after proved hom equality. -/
theorem groupCoconeComparisonIso_hom (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F)
    (e : F.flip ⋙ natQuotientColimit ≅ c.pt)
    (he : e.hom = pointwiseComparison F c) :
    (groupCoconeComparisonIso F c e).hom = groupCoconeComparisonDesc F c :=
  (congrArg (fun f => (fubiniIso F).hom ≫ f)
    (natQuotientColimit.congr_map he)).trans
      (groupCoconeComparisonDesc_fubini_word F c).symm

/-- The ENTIRE inverse comparison function retains both actual original inverse Iso maps. -/
theorem groupCoconeComparisonIso_inv (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone F)
    (e : F.flip ⋙ natQuotientColimit ≅ c.pt) :
    (groupCoconeComparisonIso F c e).inv =
      natQuotientColimit.map e.inv ≫ (fubiniIso F).inv := rfl

/-- ALL original matrix and cocone target maps preserve the ENTIRE actual pointwise comparison. -/
theorem pointwiseComparison_map_square {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}}
    (c : Cocone F) (d : Cocone G) (a : F ⟶ G) (t : c.pt ⟶ d.pt)
    (h : ∀ i, a.app i ≫ d.ι.app i = c.ι.app i ≫ t) :
    Functor.whiskerRight ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a)
        natQuotientColimit ≫ pointwiseComparison G d =
      pointwiseComparison F c ≫ t := by
  apply NatTrans.ext
  funext n
  apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.flip.obj n)).hom_ext
  intro i
  have hMap := (colimitCoconeIsColimit (F.flip.obj n)).ι_map
    (colimitCocone (G.flip.obj n)) (((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a).app n) i
  have hDesc := pointwiseDesc_fac G d n i
  have hNatural := congr_app (h i) n
  have hFac := pointwiseDesc_fac F c n i
  exact originalPointwiseLegSquare
    ((GrpCat.FilteredColimits.colimitCocone (F.flip.obj n)).ι.app i)
    (natQuotientColimit.map
      (((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a).app n))
    (pointwiseDesc G d n) ((a.app i).app n)
    ((GrpCat.FilteredColimits.colimitCocone (G.flip.obj n)).ι.app i)
    ((d.ι.app i).app n) (pointwiseDesc F c n) (t.app n) ((c.ι.app i).app n)
    hMap hDesc hNatural hFac

/-- ALL original matrix and target maps preserve the ENTIRE actual outer Group comparison. -/
theorem groupCoconeComparisonDesc_map_square {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}}
    (c : Cocone F) (d : Cocone G) (a : F ⟶ G) (t : c.pt ⟶ d.pt)
    (h : ∀ i, a.app i ≫ d.ι.app i = c.ι.app i ≫ t) :
    iteratedColimitFunctor.map a ≫ groupCoconeComparisonDesc G d =
      groupCoconeComparisonDesc F c ≫ natQuotientColimit.map t := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := natQuotientColimit
  apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (innerColimitDiagram F)).hom_ext
  intro i
  have hMap := (colimitCoconeIsColimit (innerColimitDiagram F)).ι_map
    (colimitCocone (innerColimitDiagram G)) (Functor.whiskerRight a Q) i
  have hDesc := groupCoconeComparisonDesc_fac G d i
  have hNatural : Q.map (a.app i) ≫ Q.map (d.ι.app i) =
      Q.map (c.ι.app i) ≫ Q.map t :=
    (Q.map_comp _ _).symm.trans ((Q.congr_map (h i)).trans (Q.map_comp _ _))
  have hFac := groupCoconeComparisonDesc_fac F c i
  exact originalPointwiseLegSquare
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i)
    (iteratedColimitFunctor.map a) (groupCoconeComparisonDesc G d)
    (Q.map (a.app i))
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram G)).ι.app i)
    (Q.map (d.ι.app i)) (groupCoconeComparisonDesc F c) (Q.map t) (Q.map (c.ι.app i))
    hMap hDesc hNatural hFac

end GrpCat.FilteredColimits.PointwiseComparison
