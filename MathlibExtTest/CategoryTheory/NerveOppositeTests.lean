/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.NerveOppositeNaturality

/-!
# Nerve/opposite bridge public contract

Compile-level pins for the degreewise nerve/opposite equivalence and its
`Data` and simplicial promotions, the naturality square, plus one asymmetric
degree-1 endpoint-reversal computation on `Fin 2`.
-/

open CategoryTheory Opposite

universe u v

namespace MathlibExtTest.CategoryTheory.NerveOppositeTests

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

noncomputable example (n : ℕ) :
    ComposableArrows Cᵒᵖ n ≃ ComposableArrows C n :=
  CategoryTheory.nerveOppositeEquiv C n

noncomputable example :
    CategoryTheory.nerveData Cᵒᵖ ≅
      SimplicialObject.Data.rev (CategoryTheory.nerveData C) :=
  CategoryTheory.nerveOppositeDataIso C

noncomputable example :
    nerve Cᵒᵖ ≅ SimplicialObject.opFunctor.obj (nerve C) :=
  CategoryTheory.nerveOppositeSimplicialIso C

example (H : C ⥤ D) :
    (CategoryTheory.nerveOppositeSimplicialIso C).hom ≫
        SimplicialObject.opFunctor.map (nerveMap H) =
      nerveMap H.op ≫ (CategoryTheory.nerveOppositeSimplicialIso D).hom :=
  CategoryTheory.nerveOppositeSimplicialIso_naturality H

example {n : ℕ} (i : Fin (n + 2)) :
    (Equiv.toIso (CategoryTheory.nerveOppositeEquiv C (n + 1))).hom ≫
        (SimplicialObject.Data.rev (CategoryTheory.nerveData C)).δ i =
      (CategoryTheory.nerveData Cᵒᵖ).δ i ≫
        (Equiv.toIso (CategoryTheory.nerveOppositeEquiv C n)).hom :=
  CategoryTheory.nerveOpposite_face_compat C i

example {n : ℕ} (i : Fin (n + 1)) :
    (Equiv.toIso (CategoryTheory.nerveOppositeEquiv C n)).hom ≫
        (SimplicialObject.Data.rev (CategoryTheory.nerveData C)).σ i =
      (CategoryTheory.nerveData Cᵒᵖ).σ i ≫
        (Equiv.toIso (CategoryTheory.nerveOppositeEquiv C (n + 1))).hom :=
  CategoryTheory.nerveOpposite_degeneracy_compat C i

example :
    (ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 from by decide))).op.obj 0 =
      op (1 : Fin 2) ∧
    (ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 from by decide))).op.obj 1 =
      op (0 : Fin 2) := by
  have h0 : (0 : Fin 2).rev = 1 := by decide
  have h1 : (1 : Fin 2).rev = 0 := by decide
  constructor <;>
    simp only [ComposableArrows.op_obj, h0, h1, ComposableArrows.mk₁_obj] <;>
    rfl

noncomputable example (C : Type u) [Category.{v} C] :
    (CategoryTheory.nerveOppositeNatIso.app (Cat.of C)) =
      CategoryTheory.nerveOppositeSimplicialIso C :=
  CategoryTheory.nerveOppositeNatIso_app C

example {n : ℕ} (S : ComposableArrows Cᵒᵖ n) :
    ((CategoryTheory.nerveOppositeSimplicialIso C).hom.app
      (Opposite.op (SimplexCategory.mk n))) S = S.unop :=
  CategoryTheory.nerveOppositeSimplicialIso_hom_app_mk C n S

example {n : ℕ} (S : ComposableArrows C n) :
    ((CategoryTheory.nerveOppositeSimplicialIso C).inv.app
      (Opposite.op (SimplexCategory.mk n))) S = S.op :=
  CategoryTheory.nerveOppositeSimplicialIso_inv_app_mk C n S

example :
    ((((CategoryTheory.nerveOppositeSimplicialIso (Fin 2)).inv.app
        (Opposite.op (SimplexCategory.mk 1)))
        (ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 from by decide)))).obj
        0) = op (1 : Fin 2) ∧
      ((((CategoryTheory.nerveOppositeSimplicialIso (Fin 2)).inv.app
        (Opposite.op (SimplexCategory.mk 1)))
        (ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 from by decide)))).obj
        1) = op (0 : Fin 2) := by
  have h0 : (0 : Fin 2).rev = 1 := by decide
  have h1 : (1 : Fin 2).rev = 0 := by decide
  constructor <;>
    simp only [CategoryTheory.nerveOppositeSimplicialIso_inv_app_mk,
      ComposableArrows.op_obj, h0, h1, ComposableArrows.mk₁_obj] <;>
    rfl

end MathlibExtTest.CategoryTheory.NerveOppositeTests
