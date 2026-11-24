/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
import Mathlib.CategoryTheory.Bicategory.CatEnriched

/-!
# The homotopy two-category of a simplicially enriched category

Apply the existing monoidal homotopy-category functor to the actual enriched
Hom spaces and use the native Cat-enriched strict bicategory. The original
object labels are unchanged. Individual Hom vertices give the original
one-cells; edges give two-cell classes with their complete boundaries.

This constructs the actual homotopy two-category of an enriched target.
A comparison with an arbitrary higher CSS target is a separate theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SSet

/-- The strict homotopy two-category, on the unchanged original object labels. -/
@[nolint unusedArguments]
abbrev HomotopyTwoCategory (C : Type v) [EnrichedCategory SSet.{u} C] :=
  CatEnriched (TransportEnrichment SSet.hoFunctor.{u} C)

namespace HomotopyTwoCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The original object is retained literally. -/
def objectOf (x : C) : HomotopyTwoCategory C := x

/-- Forgetting the homotopy two-category tag recovers the same original object. -/
def originalObject (x : HomotopyTwoCategory C) : C := x

@[simp]
theorem originalObject_objectOf (x : C) : originalObject (objectOf x) = x := rfl

@[simp]
theorem objectOf_originalObject (x : HomotopyTwoCategory C) : objectOf (originalObject x) = x := rfl

/-- The individual original enriched Hom vertex is the corresponding one-cell. -/
def oneCell {x y : C} (f : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    objectOf x ⟶ objectOf y := SSet.HomotopyCategory.mk f

/-- One-cells recover their original Hom vertex with both endpoints fixed. -/
def originalOneCell {x y : C} (f : objectOf x ⟶ objectOf y) :
    (x ⟶[SSet.{u}] y) _⦋0⦌ := SSet.HomotopyCategory.objEquiv f

@[simp]
theorem originalOneCell_oneCell {x y : C} (f : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    originalOneCell (oneCell f) = f := rfl

@[simp]
theorem oneCell_originalOneCell {x y : C} (f : objectOf x ⟶ objectOf y) :
    oneCell (originalOneCell f) = f := SSet.HomotopyCategory.objEquiv.symm_apply_apply f

/-- The original Hom edge, with its exact endpoints, determines a two-cell class. -/
def twoCell {x y : C} {f g : (x ⟶[SSet.{u}] y) _⦋0⦌}
    (e : SSet.Edge f g) : oneCell f ⟶ oneCell g :=
  SSet.HomotopyCategory.homMk e

/-- The identity two-cell is the same original degenerate Hom edge. -/
theorem twoCell_id {x y : C} (f : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    twoCell (SSet.Edge.id f) = 𝟙 (oneCell f) :=
  SSet.HomotopyCategory.homMk_id f

/-- The whole supplied Hom composition triangle gives the original vertical two-cell composite. -/
theorem twoCell_comp {x y : C} {f g h : (x ⟶[SSet.{u}] y) _⦋0⦌}
    {e : SSet.Edge f g} {d : SSet.Edge g h} {c : SSet.Edge f h}
    (triangle : SSet.Edge.CompStruct e d c) : twoCell e ≫ twoCell d = twoCell c :=
  SSet.HomotopyCategory.homMk_comp_homMk triangle

/-- Original enriched identities are read at the same scalar zero simplex. -/
theorem originalOneCell_identity (x : C) :
    originalOneCell (𝟙 (objectOf x)) = (eId SSet.{u} x).app _ PUnit.unit := rfl

/-- Horizontal composition of original one-cells is the original enriched composition. -/
theorem oneCell_comp {x y z : C} (f : (x ⟶[SSet.{u}] y) _⦋0⦌)
    (g : (y ⟶[SSet.{u}] z) _⦋0⦌) :
    oneCell f ≫ oneCell g = oneCell ((eComp SSet.{u} x y z).app _ ⟨f, g⟩) := rfl

/-- Horizontal composition retains the complete pair of original Hom edges. -/
def horizontalEdge {x y z : C}
    {f f' : (x ⟶[SSet.{u}] y) _⦋0⦌} {g g' : (y ⟶[SSet.{u}] z) _⦋0⦌}
    (a : SSet.Edge f f') (b : SSet.Edge g g') :
    SSet.Edge ((eComp SSet.{u} x y z).app _ ⟨f, g⟩)
      ((eComp SSet.{u} x y z).app _ ⟨f', g'⟩) :=
  (SSet.Edge.ofTruncated (a.toTruncated.tensor b.toTruncated)).map (eComp SSet.{u} x y z)

/-- Its whole simplex is the original enriched composition of the two supplied edge simplices. -/
theorem horizontalEdge_edge {x y z : C}
    {f f' : (x ⟶[SSet.{u}] y) _⦋0⦌} {g g' : (y ⟶[SSet.{u}] z) _⦋0⦌}
    (a : SSet.Edge f f') (b : SSet.Edge g g') :
    (horizontalEdge a b).edge = (eComp SSet.{u} x y z).app _ ⟨a.edge, b.edge⟩ := rfl

/-- Native horizontal composition reads that exact original paired Hom edge. -/
theorem twoCell_horizontal {x y z : C}
    {f f' : (x ⟶[SSet.{u}] y) _⦋0⦌} {g g' : (y ⟶[SSet.{u}] z) _⦋0⦌}
    (a : SSet.Edge f f') (b : SSet.Edge g g') :
    CatEnriched.hComp (twoCell a) (twoCell b) = twoCell (horizontalEdge a b) := by
  let ha : SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj (x ⟶[SSet.{u}] y)) f ⟶
      SSet.Truncated.HomotopyCategory.mk
        (V := (SSet.truncation 2).obj (x ⟶[SSet.{u}] y)) f' :=
    SSet.Truncated.HomotopyCategory.homMk
      (V := (SSet.truncation 2).obj (x ⟶[SSet.{u}] y)) a.toTruncated
  let hb : SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj (y ⟶[SSet.{u}] z)) g ⟶
      SSet.Truncated.HomotopyCategory.mk
        (V := (SSet.truncation 2).obj (y ⟶[SSet.{u}] z)) g' :=
    SSet.Truncated.HomotopyCategory.homMk
      (V := (SSet.truncation 2).obj (y ⟶[SSet.{u}] z)) b.toTruncated
  change (SSet.mapHomotopyCategory (eComp SSet.{u} x y z)).map
    ((SSet.Truncated.HomotopyCategory.BinaryProduct.inverse
      ((SSet.truncation 2).obj (x ⟶[SSet.{u}] y))
      ((SSet.truncation 2).obj (y ⟶[SSet.{u}] z))).map
      (X := (SSet.Truncated.HomotopyCategory.mk
        (V := (SSet.truncation 2).obj (x ⟶[SSet.{u}] y)) f,
        SSet.Truncated.HomotopyCategory.mk
          (V := (SSet.truncation 2).obj (y ⟶[SSet.{u}] z)) g))
      (Y := (SSet.Truncated.HomotopyCategory.mk
        (V := (SSet.truncation 2).obj (x ⟶[SSet.{u}] y)) f',
        SSet.Truncated.HomotopyCategory.mk
          (V := (SSet.truncation 2).obj (y ⟶[SSet.{u}] z)) g'))
      (ha, hb)) = _
  have h := SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_map_mkHom_homMk_homMk
    a.toTruncated b.toTruncated
  rw [h]
  rfl

/-- The homotopy two-category is genuinely a strict bicategory, by the original monoidal transport. -/
example : Bicategory.Strict (HomotopyTwoCategory C) := inferInstance

end HomotopyTwoCategory

end SSet
