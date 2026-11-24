/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import MathlibExt.CategoryTheory.NerveObjectHomULiftIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftContainedIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveUniverses

/-!
# Original nerve maps from the common maximum universe

A maximum-level category can map to an original category with independent
object and Hom universes. The resulting map acts on the original complete
chains by the original functor. It reuses the native Hom-down and Cross maps.

The inverse readback uses the existing full object/Hom lift isomorphism and
strict-Segal decoder, followed by the canonical lowering functor. Both
directions recover every original simplex and the original whole functor.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory

universe u v

namespace CategoryTheory.NerveUniverses

variable {A : Type (max u v)} [Category.{max u v} A]
  {B : Type u} [Category.{v} B]

/-- Native postcomposition from a maximum-level index into the original
category, retaining the original simplices without coefficient lifts. -/
@[expose] def nerveMapMax (F : A ⥤ B) : nerve A ⟶ nerve B :=
  nerveMapHomDown.{u, max u v, v}
    (F ⋙ ULift.upFunctor.{v, u, max u v}) ≫
      nerveMapCross (ULift.downFunctor.{v, u, max u v})

/-- Every original complete chain is mapped by the original functor. -/
theorem nerveMapMax_app (F : A ⥤ B) (n : SimplexCategoryᵒᵖ)
    (s : ComposableArrows A n.unop.len) :
    (nerveMapMax F).app n s = (F.mapComposableArrows _).obj s := rfl

/-- The original object is read back at degree zero. -/
theorem nerveMapMax_app_mk₀ (F : A ⥤ B) (x : A) :
    (nerveMapMax F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original arrow is read back at degree one. -/
theorem nerveMapMax_app_mk₁ (F : A ⥤ B) {x y : A} (f : x ⟶ y) :
    (nerveMapMax F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) := by
  change (F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f) = _
  exact ComposableArrows.ext₁ rfl rfl (by simp)

/-- Original indexing precomposition gives the original composed nerve map. -/
theorem nerveMapMax_comp {D : Type (max u v)} [Category.{max u v} D]
    (F : A ⥤ D) (G : D ⥤ B) :
    nerveMap F ≫ nerveMapMax G = nerveMapMax (F ⋙ G) := by
  ext n s
  rfl

/-- Lowering the object sort after maximum-level postcomposition preserves
the same original composite functor and every original chain. -/
theorem nerveMapMax_comp_cross {D : Type (max u v)} [Category.{v} D]
    (F : A ⥤ D) (G : D ⥤ B) :
    nerveMapMax.{max u v, v} F ≫ nerveMapCross G = nerveMapMax (F ⋙ G) := by
  ext n s
  rfl

/-- At the original equal levels this is precisely the pinned nerve map. -/
theorem nerveMapMax_eq_nerveMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) : nerveMapMax F = nerveMap F := by
  ext n s
  rfl

private def targetIso : nerve B ≅ nerve (ULift.{max u v} (ULiftHom.{max u v} B)) :=
  (SSet.uliftContainedIso.{max u v, max u v} (nerve B)).symm ≪≫
    nerveObjectHomULiftIso.{u, v, max u v, max u v} B

private def upBig : B ⥤ ULift.{max u v} (ULiftHom.{max u v} B) :=
  ULiftHom.up.{v, u, max u v} ⋙ ULift.upFunctor.{max v (max u v), u, max u v}

private def downBig : ULift.{max u v} (ULiftHom.{max u v} B) ⥤ B :=
  ULift.downFunctor.{max v (max u v), u, max u v} ⋙ ULiftHom.down.{v, u, max u v}

private theorem nerveMapMax_downBig :
    nerveMapMax (downBig (B := B)) = (targetIso (B := B)).inv := by
  ext n s
  rfl

private theorem nerveMapMax_raise (F : A ⥤ B) :
    nerveMapMax F ≫ (targetIso (B := B)).hom = nerveMap (F ⋙ upBig) := by
  ext n s
  rfl

/-- Recover the original ordinary functor from the whole native nerve map
across the independent category object and Hom universes. -/
def functorOfMapMax (φ : nerve A ⟶ nerve B) : A ⥤ B :=
  NerveUniverses.functorOfMap (φ ≫ (targetIso (B := B)).hom) ⋙ downBig

/-- The original native map, including every original simplex, is recovered. -/
theorem nerveMapMax_functorOfMapMax (φ : nerve A ⟶ nerve B) :
    nerveMapMax (functorOfMapMax φ) = φ := by
  rw [functorOfMapMax, ← nerveMapMax_comp, nerveMapMax_downBig,
    NerveUniverses.nerveMap_functorOfMap]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Reading the nerve map returns the original whole functor into `B`. -/
theorem functorOfMapMax_nerveMapMax (F : A ⥤ B) :
    functorOfMapMax (nerveMapMax F) = F := by
  rw [functorOfMapMax, nerveMapMax_raise, NerveUniverses.functorOfMap_nerveMap]
  rfl

/-- The inverse readback also specializes to the original shared-level API. -/
theorem functorOfMapMax_eq_functorOfMap {C D : Type u}
    [Category.{u} C] [Category.{u} D] (φ : nerve C ⟶ nerve D) :
    functorOfMapMax.{u, u} φ = NerveUniverses.functorOfMap φ := by
  have h : nerveMapMax.{u, u} (NerveUniverses.functorOfMap φ) = φ :=
    (nerveMapMax_eq_nerveMap _).trans (NerveUniverses.nerveMap_functorOfMap φ)
  exact (congrArg (fun ψ : nerve C ⟶ nerve D =>
    functorOfMapMax.{u, u} (A := C) (B := D) ψ) h).symm.trans
      (functorOfMapMax_nerveMapMax.{u, u} (NerveUniverses.functorOfMap φ))

end CategoryTheory.NerveUniverses
