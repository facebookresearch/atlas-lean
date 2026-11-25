/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialHomInputEquivalence

/-!
# The SAME full cosimplicial input restriction and Hom dictionary

The canonical costructured-arrow map retains every original source
object, ordinal arrow and input map. Its same full Hom restriction
commutes with the proved complete represented-input equivalences.
Original category object and Hom universes remain independent.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D E : CosimplicialObject C}

/-- The same actual original scalar Hom restriction along an entire original cosimplicial map. -/
def homSpaceRestriction (α : D ⟶ E) (X : C) : homSpace E X ⟶ homSpace D X :=
  Functor.whiskerRight (NatTrans.op α) (yoneda.obj X)

/-- The canonical original full input restriction keeps each source object and its entire
original input map. -/
def inputRestriction (α : D ⟶ E) (X : C) : CostructuredArrow E X ⥤ CostructuredArrow D X :=
  CostructuredArrow.map₂ (F := 𝟭 SimplexCategory) (G := 𝟭 C) α (𝟙 X)

/-- Every full original scalar Hom map restricts by the same entire original source map. -/
theorem homSpaceRestriction_app (α : D ⟶ E) (X : C) (n : SimplexCategory) (g : E.obj n ⟶ X) :
    (homSpaceRestriction α X).app (op n) g = α.app n ≫ g := rfl

/-- Every original full input keeps its same entire original restriction triangle. -/
theorem inputRestriction_hom (α : D ⟶ E) (X : C) (s : CostructuredArrow E X) :
    ((inputRestriction α X).obj s).hom = α.app s.left ≫ s.hom := by
  change α.app s.left ≫ (s.hom ≫ 𝟙 X) = α.app s.left ≫ s.hom
  rw [Category.comp_id]

/-- Both original complete represented-input dictionaries commute with the SAME original full
restriction. -/
def homInputEquivalenceRestriction (α : D ⟶ E) (X : C) :
    (homInputEquivalence E X).functor ⋙ inputRestriction α X ≅
      CostructuredArrow.map (S := SSet.stdSimplex.{v}) (homSpaceRestriction α X) ⋙
        (homInputEquivalence D X).functor :=
  NatIso.ofComponents (fun s => CostructuredArrow.isoMk (Iso.refl s.left) (by
    have h : SSet.yonedaEquiv (s.hom ≫ homSpaceRestriction α X) =
        α.app s.left ≫ SSet.yonedaEquiv s.hom :=
      SSet.yonedaEquiv_comp s.hom (homSpaceRestriction α X)
    change D.map (𝟙 s.left) ≫ SSet.yonedaEquiv (s.hom ≫ homSpaceRestriction α X) =
      ((inputRestriction α X).obj (CostructuredArrow.mk (SSet.yonedaEquiv s.hom))).hom
    exact (congrArg (fun f => f ≫ SSet.yonedaEquiv (s.hom ≫ homSpaceRestriction α X))
      (D.map_id s.left)).trans
      ((Category.id_comp _).trans (h.trans
        (inputRestriction_hom α X (CostructuredArrow.mk (SSet.yonedaEquiv s.hom))).symm))))
    (by
      intro s t f
      apply CostructuredArrow.hom_ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end CategoryTheory.CosimplicialObject
