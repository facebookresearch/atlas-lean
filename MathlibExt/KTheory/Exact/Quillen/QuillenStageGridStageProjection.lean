/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import MathlibExt.KTheory.Exact.Quillen.QuillenEdgewiseStageNerve
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridNerve

/-!
# The Quillen Stage-grid projection on nerves

The material-Stage projection from a Quillen Stage-grid lift has different
hom universes in its source and target.  Applying `nerveMapHomDown`
degreewise gives a natural transformation from the Stage-grid nerve to the
outer-edgewise weak-Stage nerve, and applying the simplicial diagonal gives
the corresponding map of simplicial sets.

This file constructs only these maps and their component formulas.  It makes
no degreewise-equivalence, realization weak-equivalence, outer-edgewise
removal, pointed, loop, or Q/S comparison claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageGridStageProjectionWaldhausenCategory :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The levelwise nerve map induced by projection from a Quillen Stage-grid
lift to its material weak Stage. -/
noncomputable def quillenStageGridStageProjectionNerve :
    quillenStageGridNerve C ⟶ edgewiseStageWeakNerve C where
  app a := CategoryTheory.nerveMapHomDown
    (quillenStageGridProjection C a.unop)
  naturality {a b} f := by
    change CategoryTheory.nerveMap
          (reindexQuillenStageGridLift (C := C) f.unop) ≫
        CategoryTheory.nerveMapHomDown
          (quillenStageGridProjection C b.unop) =
      CategoryTheory.nerveMapHomDown
          (quillenStageGridProjection C a.unop) ≫
        CategoryTheory.nerveMap
          (edgewiseStageWeakReindex (C := C) f.unop)
    rw [CategoryTheory.nerveMap_nerveMapHomDown_comp,
      CategoryTheory.nerveMapHomDown_nerveMap_comp,
      reindexQuillenStageGridLift_comp_gridProjection]

/-- Component of the levelwise Stage-grid projection. -/
@[simp]
theorem quillenStageGridStageProjectionNerve_app
    (a : SimplexCategoryᵒᵖ) :
    (quillenStageGridStageProjectionNerve (C := C)).app a =
      CategoryTheory.nerveMapHomDown
        (quillenStageGridProjection C a.unop) :=
  rfl

/-- The levelwise Stage-grid projection sends a vertex to its material weak
Stage. -/
@[simp]
theorem quillenStageGridStageProjectionNerve_app_app_mk₀
    (a : SimplexCategoryᵒᵖ) (X : QuillenStageGridLift C a.unop) :
    ((quillenStageGridStageProjectionNerve (C := C)).app a).app
        (op ⦋0⦌) (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀
        X.grid :=
  CategoryTheory.nerveMapHomDown_app_mk₀ _ _

/-- The levelwise Stage-grid projection sends an edge to its material-grid
morphism. -/
@[simp]
theorem quillenStageGridStageProjectionNerve_app_app_mk₁
    (a : SimplexCategoryᵒᵖ) {X Y : QuillenStageGridLift C a.unop}
    (f : X ⟶ Y) :
    ((quillenStageGridStageProjectionNerve (C := C)).app a).app
        (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁
        f.hom.left :=
  CategoryTheory.nerveMapHomDown_app_mk₁ _

/-- The diagonal map induced by the levelwise Quillen Stage-grid projection. -/
noncomputable def quillenStageGridStageProjectionDiagonal :
    quillenStageGridDiagonal C ⟶ edgewiseStageWeakDiagonal C :=
  SSet.simplicialDiagonalFunctor.map
    (quillenStageGridStageProjectionNerve (C := C))

/-- Degreewise component of the diagonal Stage-grid projection. -/
@[simp]
theorem quillenStageGridStageProjectionDiagonal_app
    (a : SimplexCategoryᵒᵖ) :
    (quillenStageGridStageProjectionDiagonal (C := C)).app a =
      (CategoryTheory.nerveMapHomDown
        (quillenStageGridProjection C a.unop)).app a :=
  rfl

/-- The diagonal Stage-grid projection sends a vertex to its material weak
Stage. -/
@[simp]
theorem quillenStageGridStageProjectionDiagonal_app_mk₀
    (X : QuillenStageGridLift C ⦋0⦌) :
    (quillenStageGridStageProjectionDiagonal (C := C)).app
        (op ⦋0⦌) (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀
        X.grid :=
  CategoryTheory.nerveMapHomDown_app_mk₀ _ _

/-- The diagonal Stage-grid projection sends an edge to its material-grid
morphism. -/
@[simp]
theorem quillenStageGridStageProjectionDiagonal_app_mk₁
    {X Y : QuillenStageGridLift C ⦋1⦌} (f : X ⟶ Y) :
    (quillenStageGridStageProjectionDiagonal (C := C)).app
        (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁
        f.hom.left :=
  CategoryTheory.nerveMapHomDown_app_mk₁ _

end AlgebraicKTheory

end
