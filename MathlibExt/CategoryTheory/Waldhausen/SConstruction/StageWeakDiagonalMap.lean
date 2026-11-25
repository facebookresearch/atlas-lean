/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonal
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakNerveMap

/-!
# Exact-functor maps on the weak-stage diagonal

For exact categories `C` and `D` over the same universes `u, v` with their
local standard Waldhausen structures (`ExactCategory.waldhausenCategory`),
an additive exact functor `F : C ⥤ D` induces
`stageWeakDiagonalMap F : stageWeakDiagonal C ⟶ stageWeakDiagonal D`
as `SSet.simplicialDiagonalFunctor.map (stageWeakNerveMap C D F)`.

Only the degree-`a` component law, the identity/composition laws reusing
`stageWeakNerveMap_id`/`comp` with functoriality, degree-zero `mk₀` and
degree-one `mk₁` action laws reusing the corresponding weak-nerve formulas,
and the mapped-zero `stageWeakDiagonalMap_zeroVertex` specialization are
added.

Nonclaims: no realization, additivity, π₀/K₀ identification, G-theory,
spectra, Q/S comparison, new structure/class, or second diagonal.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Exact-functor map on the weak-stage diagonal via the nerve map. -/
def stageWeakDiagonalMap :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonal C ⟶ stageWeakDiagonal D) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact SSet.simplicialDiagonalFunctor.map (stageWeakNerveMap C D F)

/-- Component computation for `stageWeakDiagonalMap`. -/
@[simp]
theorem stageWeakDiagonalMap_app (a : SimplexCategoryᵒᵖ) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalMap C D F).app a =
        ((stageWeakNerveMap C D F).app a).app a) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  unfold stageWeakDiagonalMap
  rfl

/-- Identity functor induces the identity weak-stage diagonal map. -/
@[simp]
theorem stageWeakDiagonalMap_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalMap C C (𝟭 C) = 𝟙 (stageWeakDiagonal C)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  ext a
  simp only [stageWeakDiagonalMap_app, stageWeakNerveMap_id, NatTrans.id_app,
    stageWeakDiagonal_obj]

/-- Composite functors induce composite weak-stage diagonal maps. -/
@[simp]
theorem stageWeakDiagonalMap_comp (E : Type u) [Category.{v} E]
    [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      stageWeakDiagonalMap C E (F ⋙ G) =
        stageWeakDiagonalMap C D F ≫ stageWeakDiagonalMap D E G) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  ext a
  simp only [stageWeakDiagonalMap_app, stageWeakNerveMap_comp, NatTrans.comp_app]
  rfl

/-- Degree-zero `mk₀` action of a weak-stage diagonal map. -/
@[simp]
theorem stageWeakDiagonalMap_app_mk₀
    (X : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C 0)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalMap C D F).app (op ⦋0⦌) (ComposableArrows.mk₀ X) =
        ComposableArrows.mk₀ ((mapStageWeak C D F 0).obj X)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rw [stageWeakDiagonalMap_app]
  exact stageWeakNerveMap_app_mk₀ C D F (op ⦋0⦌) X

/-- Degree-one `mk₁` action of a weak-stage diagonal map. -/
@[simp]
theorem stageWeakDiagonalMap_app_mk₁
    {X Y : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C 1)} (φ : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalMap C D F).app (op ⦋1⦌)
          (ComposableArrows.mk₁ φ) =
        ComposableArrows.mk₁ ((mapStageWeak C D F 1).map φ)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rw [stageWeakDiagonalMap_app]
  exact stageWeakNerveMap_app_mk₁ C D F (op ⦋1⦌) φ

/-- Mapped-zero vertex as the image of the zero vertex. -/
@[simp]
theorem stageWeakDiagonalMap_zeroVertex :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalMap C D F).app (op ⦋0⦌) (stageWeakDiagonalZeroVertex C) =
        ComposableArrows.mk₀ ((mapStageWeak C D F 0).obj ⟨stageZero C⟩)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  simp only [stageWeakDiagonalZeroVertex, stageWeakDiagonalMap_app_mk₀]
  rfl

end CategoryTheory.Waldhausen.SConstruction
