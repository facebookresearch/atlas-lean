/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Index and ambient isomorphisms of original join-slice restrictions

Changing the indexing diagram by an actual isomorphism retains every
original joined simplex. Compatible isomorphisms of a pair of indexing
shapes give actual arrow isomorphisms of both original slice restrictions.
Ambient isomorphisms preserve the same whole under- and over-slice maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet.sliceOver

variable {K L C D C' D' : SSet.{u}}

/-- Equality of the fixed diagram preserves the entire original joined map. -/
theorem fixedDiagramEq_app_val {X : SSet.{u}} {f g : K ⟶ X} (h : f = g)
    (n : SimplexCategoryᵒᵖ) (s : (sliceOver X f).obj n) :
    (((eqToHom (congrArg (sliceOver X) h)).app n s).1) = s.1 := by
  cases h
  rfl

/-- The original restriction along an index isomorphism is an isomorphism. -/
def indexIso (X : SSet.{u}) (f : K ⟶ X) (e : L ≅ K) :
    sliceOver X f ≅ sliceOver X (e.hom ≫ f) :=
  NatIso.ofComponents (fun n => Equiv.toIso {
    toFun := fun s => (restrict X f e.hom).app n s
    invFun := fun s => ⟨(join.obj (stdSimplex.obj n.unop)).map e.inv ≫ s.1, by
      rw [← Category.assoc, ← map_comp_joinInr, Category.assoc, s.2,
        ← Category.assoc, e.inv_hom_id, Category.id_comp]⟩
    left_inv := by
      intro s
      apply Subtype.ext
      change (join.obj (stdSimplex.obj n.unop)).map e.inv ≫
        ((join.obj (stdSimplex.obj n.unop)).map e.hom ≫ s.1) = s.1
      rw [← Category.assoc, ← (join.obj (stdSimplex.obj n.unop)).map_comp,
        e.inv_hom_id, (join.obj (stdSimplex.obj n.unop)).map_id, Category.id_comp]
    right_inv := by
      intro s
      apply Subtype.ext
      change (join.obj (stdSimplex.obj n.unop)).map e.hom ≫
        ((join.obj (stdSimplex.obj n.unop)).map e.inv ≫ s.1) = s.1
      rw [← Category.assoc, ← (join.obj (stdSimplex.obj n.unop)).map_comp,
        e.hom_inv_id, (join.obj (stdSimplex.obj n.unop)).map_id, Category.id_comp] })
    (by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro s
      exact NatTrans.naturality_apply (restrict X f e.hom) α s)

/-- The index comparison keeps the original restriction map. -/
theorem indexIso_hom (X : SSet.{u}) (f : K ⟶ X) (e : L ≅ K) :
    (indexIso X f e).hom = restrict X f e.hom := rfl

/-- Compatible changes of both index shapes preserve the original
square-to-subdiagram restriction as an actual arrow isomorphism. -/
def restrictionIndexArrowIso (X : SSet.{u}) (q : D ⟶ X)
    (i : C ⟶ D) (i' : C' ⟶ D') (eD : D' ≅ D) (eC : C' ≅ C)
    (h : i' ≫ eD.hom = eC.hom ≫ i) :
    Arrow.mk (restrict X q i) ≅ Arrow.mk (restrict X (eD.hom ≫ q) i') := by
  let htarget : eC.hom ≫ (i ≫ q) = i' ≫ (eD.hom ≫ q) := by
    rw [← Category.assoc, ← h, Category.assoc]
  let etarget : sliceOver X (i ≫ q) ≅ sliceOver X (i' ≫ (eD.hom ≫ q)) :=
    indexIso X (i ≫ q) eC ≪≫ eqToIso (congrArg (sliceOver X) htarget)
  refine Arrow.isoMk (indexIso X q eD) etarget ?_
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  have hc := fixedDiagramEq_app_val htarget n
    ((restrict X (i ≫ q) eC.hom).app n ((restrict X q i).app n s))
  calc
    (((indexIso X q eD).hom ≫ restrict X (eD.hom ≫ q) i').app n s).1 =
        (join.obj (stdSimplex.obj n.unop)).map i' ≫
          ((join.obj (stdSimplex.obj n.unop)).map eD.hom ≫ s.1) := rfl
    _ = (join.obj (stdSimplex.obj n.unop)).map eC.hom ≫
          ((join.obj (stdSimplex.obj n.unop)).map i ≫ s.1) := by
      rw [← Category.assoc, ← (join.obj (stdSimplex.obj n.unop)).map_comp,
        h, (join.obj (stdSimplex.obj n.unop)).map_comp, Category.assoc]
    _ = ((restrict X (i ≫ q) eC.hom).app n ((restrict X q i).app n s)).1 := rfl
    _ = ((restrict X q i ≫ etarget.hom).app n s).1 := hc.symm

/-- Every boundary-lifting condition is unchanged by those exact
indexing isomorphisms and their original commuting inclusion. -/
theorem hasLiftingProperty_restrictionIndex_iff (X : SSet.{u}) (q : D ⟶ X)
    (i : C ⟶ D) (i' : C' ⟶ D') (eD : D' ≅ D) (eC : C' ≅ C)
    (h : i' ≫ eD.hom = eC.hom ≫ i)
    {A B : SSet.{u}} (b : A ⟶ B) :
    HasLiftingProperty b (restrict X q i) ↔
      HasLiftingProperty b (restrict X (eD.hom ≫ q) i') :=
  HasLiftingProperty.iff_of_arrow_iso_right b (restrictionIndexArrowIso X q i i' eD eC h)

end SSet.sliceOver

namespace SSet.sliceUnder

variable {X K L C D C' D' : SSet.{u}}

/-- Equality of the fixed under-diagram retains each original whole joined map. -/
theorem fixedDiagramEq_app_val {L : SSet.{u}} {f g : L ⟶ X} (h : f = g)
    (n : SimplexCategoryᵒᵖ) (s : (sliceUnder X f).obj n) :
    ((eqToHom (congrArg (sliceUnder X) h)).app n s).val = s.val := by
  cases h
  rfl


/-- Original under-slice restriction along an actual index isomorphism is an isomorphism. -/
def indexIso (X : SSet.{u}) (f : K ⟶ X) (e : L ≅ K) :
    sliceUnder X f ≅ sliceUnder X (e.hom ≫ f) :=
  NatIso.ofComponents (fun n => Equiv.toIso {
    toFun := fun s => (restrict X f e.hom).app n s
    invFun := fun s => ⟨(join.map e.inv).app (stdSimplex.obj n.unop) ≫ s.val, by
      rw [← Category.assoc, ← map_comp_joinInl, Category.assoc, s.property,
        ← Category.assoc, e.inv_hom_id, Category.id_comp]⟩
    left_inv := by
      intro s
      apply Subtype.ext
      change (join.map e.inv).app (stdSimplex.obj n.unop) ≫
        ((join.map e.hom).app (stdSimplex.obj n.unop) ≫ s.val) = s.val
      rw [← Category.assoc, ← NatTrans.comp_app, ← join.map_comp,
        e.inv_hom_id, join.map_id, NatTrans.id_app, Category.id_comp]
    right_inv := by
      intro s
      apply Subtype.ext
      change (join.map e.hom).app (stdSimplex.obj n.unop) ≫
        ((join.map e.inv).app (stdSimplex.obj n.unop) ≫ s.val) = s.val
      rw [← Category.assoc, ← NatTrans.comp_app, ← join.map_comp,
        e.hom_inv_id, join.map_id, NatTrans.id_app, Category.id_comp] })
    (by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro s
      exact NatTrans.naturality_apply (restrict X f e.hom) α s)

/-- The index isomorphism keeps the literal original under-slice restriction. -/
theorem indexIso_hom (X : SSet.{u}) (f : K ⟶ X) (e : L ≅ K) :
    (indexIso X f e).hom = restrict X f e.hom := rfl

/-- Compatible changes of both index shapes retain the actual under-slice restriction arrow. -/
def restrictionIndexArrowIso (X : SSet.{u}) (q : D ⟶ X)
    (i : C ⟶ D) (i' : C' ⟶ D') (eD : D' ≅ D) (eC : C' ≅ C)
    (h : i' ≫ eD.hom = eC.hom ≫ i) :
    Arrow.mk (restrict X q i) ≅ Arrow.mk (restrict X (eD.hom ≫ q) i') := by
  let htarget : eC.hom ≫ (i ≫ q) = i' ≫ (eD.hom ≫ q) := by
    rw [← Category.assoc, ← h, Category.assoc]
  let etarget : sliceUnder X (i ≫ q) ≅ sliceUnder X (i' ≫ (eD.hom ≫ q)) :=
    indexIso X (i ≫ q) eC ≪≫ eqToIso (congrArg (sliceUnder X) htarget)
  refine Arrow.isoMk (indexIso X q eD) etarget ?_
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  have hc := fixedDiagramEq_app_val htarget n
    ((restrict X (i ≫ q) eC.hom).app n ((restrict X q i).app n s))
  calc
    (((indexIso X q eD).hom ≫ restrict X (eD.hom ≫ q) i').app n s).val =
        (join.map i').app (stdSimplex.obj n.unop) ≫
          ((join.map eD.hom).app (stdSimplex.obj n.unop) ≫ s.val) := rfl
    _ = (join.map eC.hom).app (stdSimplex.obj n.unop) ≫
        ((join.map i).app (stdSimplex.obj n.unop) ≫ s.val) := by
      rw [← Category.assoc, ← NatTrans.comp_app, ← join.map_comp,
        h, join.map_comp, NatTrans.comp_app, Category.assoc]
    _ = ((restrict X (i ≫ q) eC.hom).app n ((restrict X q i).app n s)).val := rfl
    _ = ((restrict X q i ≫ etarget.hom).app n s).val := hc.symm

/-- Boundary lifting is unchanged by the actual compatible under-diagram isomorphisms. -/
theorem hasLiftingProperty_restrictionIndex_iff (X : SSet.{u}) (q : D ⟶ X)
    (i : C ⟶ D) (i' : C' ⟶ D') (eD : D' ≅ D) (eC : C' ≅ C)
    (h : i' ≫ eD.hom = eC.hom ≫ i) {A B : SSet.{u}} (b : A ⟶ B) :
    HasLiftingProperty b (restrict X q i) ↔
      HasLiftingProperty b (restrict X (eD.hom ≫ q) i') :=
  HasLiftingProperty.iff_of_arrow_iso_right b (restrictionIndexArrowIso X q i i' eD eC h)

end SSet.sliceUnder

namespace SSet.sliceUnder

/-- The original under-slice restriction transports as an arrow under an ambient isomorphism. -/
def restrictionAmbientArrowIso {X Y C D : SSet.{u}} (q : D ⟶ X) (i : C ⟶ D) (e : X ≅ Y) :
    Arrow.mk (restrict X q i) ≅ Arrow.mk (restrict Y (q ≫ e.hom) i) := by
  let eD : Under.mk q ≅ Under.mk (q ≫ e.hom) := Under.isoMk e rfl
  let eC : Under.mk (i ≫ q) ≅ Under.mk (i ≫ (q ≫ e.hom)) :=
    Under.isoMk e (Category.assoc i q e.hom)
  refine Arrow.isoMk ((joinLeftDivision D).mapIso eD)
    ((joinLeftDivision C).mapIso eC) ?_
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (join.map i).app (stdSimplex.obj n.unop) ≫ (s.val ≫ e.hom) =
    ((join.map i).app (stdSimplex.obj n.unop) ≫ s.val) ≫ e.hom
  exact (Category.assoc _ _ _).symm

/-- Every original boundary lifting condition is invariant under this actual
under-slice transport. -/
theorem hasLiftingProperty_restrictionAmbient_iff {X Y C D : SSet.{u}}
    (q : D ⟶ X) (i : C ⟶ D) (e : X ≅ Y) {A B : SSet.{u}} (b : A ⟶ B) :
    HasLiftingProperty b (restrict X q i) ↔
      HasLiftingProperty b (restrict Y (q ≫ e.hom) i) :=
  HasLiftingProperty.iff_of_arrow_iso_right b (restrictionAmbientArrowIso q i e)

end SSet.sliceUnder

namespace SSet.sliceOver

variable {X Y C D : SSet.{u}}

/-- An ambient isomorphism transports the original restriction as an actual arrow isomorphism. -/
def restrictionAmbientArrowIso (q : D ⟶ X) (i : C ⟶ D) (e : X ≅ Y) :
    Arrow.mk (restrict X q i) ≅ Arrow.mk (restrict Y (q ≫ e.hom) i) := by
  let eD : Under.mk q ≅ Under.mk (q ≫ e.hom) := Under.isoMk e rfl
  let eC : Under.mk (i ≫ q) ≅ Under.mk (i ≫ (q ≫ e.hom)) :=
    Under.isoMk e (Category.assoc i q e.hom)
  refine Arrow.isoMk ((joinRightDivision D).mapIso eD)
    ((joinRightDivision C).mapIso eC) ?_
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (join.obj (stdSimplex.obj n.unop)).map i ≫ (s.val ≫ e.hom) =
    ((join.obj (stdSimplex.obj n.unop)).map i ≫ s.val) ≫ e.hom
  exact (Category.assoc _ _ _).symm

/-- Every original lifting condition is invariant under the actual ambient isomorphism. -/
theorem hasLiftingProperty_restrictionAmbient_iff (q : D ⟶ X) (i : C ⟶ D) (e : X ≅ Y)
    {A B : SSet.{u}} (b : A ⟶ B) :
    HasLiftingProperty b (restrict X q i) ↔
      HasLiftingProperty b (restrict Y (q ≫ e.hom) i) :=
  HasLiftingProperty.iff_of_arrow_iso_right b (restrictionAmbientArrowIso q i e)

end SSet.sliceOver
