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

public import MathlibExt.CategoryTheory.ExactCategory.NineLemma
public import MathlibExt.CategoryTheory.ExactCategory.Opposite

/-!
# The top-row direction of the admissible three-by-three lemma

Reverse both directions of the ordinary three-by-three diagram and apply
the bottom-row theorem in the named opposite exact structure.
-/

public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private def reverseNineDiagram (D : ShortComplex (ShortComplex C)) :
    ShortComplex (ShortComplex Cᵒᵖ) :=
  ShortComplex.mk (ShortComplex.opMap D.g) (ShortComplex.opMap D.f) (by
    ext
    · have h : D.f.τ₃ ≫ D.g.τ₃ = 0 := by
        simpa only [ShortComplex.comp_τ₃, ShortComplex.zero_τ₃] using
          congrArg ShortComplex.Hom.τ₃ D.zero
      simp only [ShortComplex.comp_τ₁, ShortComplex.zero_τ₁, ShortComplex.opMap]
      dsimp only [ShortComplex.op]
      simp only [unop_comp, Quiver.Hom.unop_op]
      have hz : (0 : Opposite.op D.X₃.X₃ ⟶ Opposite.op D.X₁.X₃).unop =
          (0 : D.X₁.X₃ ⟶ D.X₃.X₃) :=
        (CategoryTheory.unopHom (Opposite.op D.X₃.X₃) (Opposite.op D.X₁.X₃)).map_zero
      exact h.trans hz.symm
    · have h : D.f.τ₂ ≫ D.g.τ₂ = 0 := by
        simpa only [ShortComplex.comp_τ₂, ShortComplex.zero_τ₂] using
          congrArg ShortComplex.Hom.τ₂ D.zero
      simp only [ShortComplex.comp_τ₂, ShortComplex.zero_τ₂, ShortComplex.opMap]
      dsimp only [ShortComplex.op]
      simp only [unop_comp, Quiver.Hom.unop_op]
      have hz : (0 : Opposite.op D.X₃.X₂ ⟶ Opposite.op D.X₁.X₂).unop =
          (0 : D.X₁.X₂ ⟶ D.X₃.X₂) :=
        (CategoryTheory.unopHom (Opposite.op D.X₃.X₂) (Opposite.op D.X₁.X₂)).map_zero
      exact h.trans hz.symm
    · have h : D.f.τ₁ ≫ D.g.τ₁ = 0 := by
        simpa only [ShortComplex.comp_τ₁, ShortComplex.zero_τ₁] using
          congrArg ShortComplex.Hom.τ₁ D.zero
      simp only [ShortComplex.comp_τ₃, ShortComplex.zero_τ₃, ShortComplex.opMap]
      dsimp only [ShortComplex.op]
      simp only [unop_comp, Quiver.Hom.unop_op]
      have hz : (0 : Opposite.op D.X₃.X₁ ⟶ Opposite.op D.X₁.X₁).unop =
          (0 : D.X₁.X₁ ⟶ D.X₃.X₁) :=
        (CategoryTheory.unopHom (Opposite.op D.X₃.X₁) (Opposite.op D.X₁.X₁)).map_zero
      exact h.trans hz.symm)

/-- In an ordinary commuting three-by-three diagram, admissible exactness
of every column and of the middle and bottom rows implies admissible
exactness of the top row. -/
theorem isAdmissibleExact_top_of_three_by_three
    (D : ShortComplex (ShortComplex C))
    (hB : IsAdmissibleExact D.X₂) (hZ : IsAdmissibleExact D.X₃)
    (h₁ : IsAdmissibleExact (D.map (ShortComplex.π₁ : ShortComplex C ⥤ C)))
    (h₂ : IsAdmissibleExact (D.map (ShortComplex.π₂ : ShortComplex C ⥤ C)))
    (h₃ : IsAdmissibleExact (D.map (ShortComplex.π₃ : ShortComplex C ⥤ C))) :
    IsAdmissibleExact D.X₁ := by
  let : ExactCategory Cᵒᵖ := oppositeExactCategory C
  let R := reverseNineDiagram D
  have hR₁ : IsAdmissibleExact R.X₁ := isAdmissibleExact_op C hZ
  have hR₂ : IsAdmissibleExact R.X₂ := isAdmissibleExact_op C hB
  have hc₁ : IsAdmissibleExact (R.map (ShortComplex.π₁ : ShortComplex Cᵒᵖ ⥤ Cᵒᵖ)) :=
    isAdmissibleExact_op C h₃
  have hc₂ : IsAdmissibleExact (R.map (ShortComplex.π₂ : ShortComplex Cᵒᵖ ⥤ Cᵒᵖ)) :=
    isAdmissibleExact_op C h₂
  have hc₃ : IsAdmissibleExact (R.map (ShortComplex.π₃ : ShortComplex Cᵒᵖ ⥤ Cᵒᵖ)) :=
    isAdmissibleExact_op C h₁
  have hR₃ := isAdmissibleExact_bottom_of_three_by_three R hR₁ hR₂ hc₁ hc₂ hc₃
  have hA : IsAdmissibleExact D.X₁.op.unop :=
    (oppositeExactCategory_isAdmissibleExact_iff C D.X₁.op).mp hR₃
  exact isAdmissibleExact_of_iso (ShortComplex.opUnop D.X₁) hA

end CategoryTheory.ExactCategory
