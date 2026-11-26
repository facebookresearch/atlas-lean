/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.TensorCotensor
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The discrete-inner embedding and zeroth-row adjunction

A simplicial space has outer degree `m` and inner degree `n`. Its zeroth
row consists of the inner vertices in every outer degree. The existing
`SSet.simplicialSpaceDiscrete` is left adjoint to this restriction. The
counit repeats an inner vertex along the unique map `[n] → [0]`.

This is the raw adjunction `p₁* ⊣ i₁*` of Joyal–Tierney, §4. No model,
Reedy, locality or Quillen property is assumed or asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Rezk

/-- Restrict a simplicial space to inner degree zero in every outer degree. -/
abbrev zerothRow : SimplicialObject SSet.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌))

/-- Zeroth-row restriction evaluates the inner zero component of a map. -/
@[simp]
lemma zerothRow_map_app {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y)
    (m : SimplexCategoryᵒᵖ) :
    (zerothRow.map f).app m = (f.app m).app (op ⦋0⦌) := rfl

private def extendVertex {A : SSet.{u}} {X : SimplicialObject SSet.{u}}
    (f : A ⟶ zerothRow.obj X) : simplicialSpaceDiscrete.obj A ⟶ X where
  app m :=
    { app := fun n => f.app m ≫ (X.obj m).map (SimplexCategory.const n.unop ⦋0⦌ 0).op
      naturality := by
        intro n k a
        change 𝟙 _ ≫ f.app m ≫
            (X.obj m).map (SimplexCategory.const k.unop ⦋0⦌ 0).op =
          (f.app m ≫ (X.obj m).map (SimplexCategory.const n.unop ⦋0⦌ 0).op) ≫
            (X.obj m).map a
        simp only [Category.id_comp]
        have h : (SimplexCategory.const n.unop ⦋0⦌ 0).op ≫ a =
            (SimplexCategory.const k.unop ⦋0⦌ 0).op := by
          apply Quiver.Hom.unop_inj
          exact Subsingleton.elim _ _
        rw [Category.assoc, ← (X.obj m).map_comp, h] }
  naturality := by
    intro m k a
    apply NatTrans.ext
    funext n
    have h := f.naturality a
    change A.map a ≫ f.app k =
      f.app m ≫ (X.map a).app (op ⦋0⦌) at h
    change A.map a ≫ (f.app k ≫ (X.obj k).map _) =
      (f.app m ≫ (X.obj m).map _) ≫ (X.map a).app n
    rw [← Category.assoc, h, Category.assoc]
    rw [← (X.map a).naturality]
    simp only [Category.assoc]

private def rowHomEquiv (A : SSet.{u}) (X : SimplicialObject SSet.{u}) :
    (simplicialSpaceDiscrete.obj A ⟶ X) ≃ (A ⟶ zerothRow.obj X) where
  toFun f :=
    { app := fun m => (f.app m).app (op ⦋0⦌)
      naturality := by
        intro m k a
        exact congrArg (fun h => h.app (op ⦋0⦌)) (f.naturality a) }
  invFun := extendVertex
  left_inv f := by
    apply NatTrans.ext
    funext m
    apply NatTrans.ext
    funext n
    have h := (f.app m).naturality (SimplexCategory.const n.unop ⦋0⦌ 0).op
    change (f.app m).app (op ⦋0⦌) ≫ (X.obj m).map _ = (f.app m).app n
    change 𝟙 _ ≫ (f.app m).app n = (f.app m).app (op ⦋0⦌) ≫ (X.obj m).map _ at h
    simpa only [Category.id_comp] using h.symm
  right_inv f := by
    apply NatTrans.ext
    funext m
    change f.app m ≫ (X.obj m).map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = f.app m
    have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [h, op_id, (X.obj m).map_id]
    exact Category.comp_id (f.app m)

/-- The actual discrete-inner embedding is left adjoint to zeroth-row restriction. -/
noncomputable def zerothRowAdjunction : simplicialSpaceDiscrete.{u} ⊣ zerothRow.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := rowHomEquiv
      homEquiv_naturality_left_symm := by
        intro A B X f g
        apply NatTrans.ext
        funext m
        apply NatTrans.ext
        funext n
        change (f.app m ≫ g.app m) ≫ (X.obj m).map _ =
          f.app m ≫ (g.app m ≫ (X.obj m).map _)
        exact Category.assoc _ _ _
      homEquiv_naturality_right := by
        intro A X Y f g
        rfl }

/-- The hom-equivalence evaluates a map at inner degree zero. -/
lemma zerothRowAdjunction_homEquiv_app (A : SSet.{u})
    (X : SimplicialObject SSet.{u}) (f : simplicialSpaceDiscrete.obj A ⟶ X)
    (m : SimplexCategoryᵒᵖ) :
    (zerothRowAdjunction.homEquiv A X f).app m =
      (f.app m).app (op ⦋0⦌) := by
  rfl

/-- The counit in bidegree `(m,n)` repeats a vertex through `[n] → [0]`. -/
@[simp]
lemma zerothRowAdjunction_counit_app (X : SimplicialObject SSet.{u})
    (m n : SimplexCategoryᵒᵖ) :
    ((zerothRowAdjunction.counit.app X).app m).app n =
      (X.obj m).map (SimplexCategory.const n.unop ⦋0⦌ 0).op := by
  simp [zerothRowAdjunction, rowHomEquiv, extendVertex]

/-- The unit is the identity under the canonical zeroth-row identification. -/
@[simp]
lemma zerothRowAdjunction_unit_app (A : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    (zerothRowAdjunction.unit.app A).app m = 𝟙 (A.obj m) := rfl

/-- The raw unit is an isomorphism. -/
instance (A : SSet.{u}) : IsIso (zerothRowAdjunction.unit.app A) := by
  refine ⟨⟨(show zerothRow.obj (simplicialSpaceDiscrete.obj A) ⟶ A from 𝟙 A),
    ?_, ?_⟩⟩
  · ext m x
    rfl
  · ext m x
    rfl

/-- The left triangle, for the original discrete embedding. -/
lemma zerothRowAdjunction_left_triangle (A : SSet.{u}) :
    simplicialSpaceDiscrete.map (zerothRowAdjunction.unit.app A) ≫
      zerothRowAdjunction.counit.app (simplicialSpaceDiscrete.obj A) =
        𝟙 (simplicialSpaceDiscrete.obj A) :=
  zerothRowAdjunction.left_triangle_components A

/-- The right triangle, for the original zeroth-row restriction. -/
lemma zerothRowAdjunction_right_triangle (X : SimplicialObject SSet.{u}) :
    zerothRowAdjunction.unit.app (zerothRow.obj X) ≫
      zerothRow.map (zerothRowAdjunction.counit.app X) = 𝟙 (zerothRow.obj X) :=
  zerothRowAdjunction.right_triangle_components X

end SSet.Rezk
