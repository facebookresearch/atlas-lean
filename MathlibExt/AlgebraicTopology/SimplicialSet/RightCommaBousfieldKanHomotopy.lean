/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKan
public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Rowwise homotopy supplied by right-comma arrows

For `d : D`, an object of `CostructuredArrow F d` carries its defining arrow
`F c ⟶ d`.  These arrows form a natural transformation from the comma
projection followed by `F` to the constant functor at `d`, hence a simplicial
homotopy between the corresponding nerve maps.

This file records only the rowwise homotopy and its exact endpoints.  It does
not assemble a homotopy on a Bousfield--Kan diagonal and makes no realization,
weak-equivalence, homotopy-fiber, or Quillen-Theorem-A claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Simplicial

namespace SSet

universe u v w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The natural transformation whose component is the defining arrow of a
right-comma object. -/
def rightCommaArrowNatTrans (F : C ⥤ D) (d : D) :
    rightCommaProjectionFunctor.{u, v, w} F d ⋙ F ⟶
      (Functor.const ((CostructuredArrow.functor F).obj d : Type (max u v w))).obj d where
  app X := by
    change CostructuredArrow F d at X
    exact X.hom
  naturality X Y f := by
    change F.map f.left ≫ Y.hom = X.hom ≫ 𝟙 d
    rw [Category.comp_id]
    exact CostructuredArrow.w f

@[simp]
theorem rightCommaArrowNatTrans_app (F : C ⥤ D) (d : D)
    (X : CostructuredArrow F d) :
    (rightCommaArrowNatTrans F d).app X = X.hom :=
  rfl

/-- Nerving the comma-arrow natural transformation gives a homotopy from the
projected comma nerve followed by `nerveMap F` to the constant-at-`d` nerve
map.  The orientation is projection at endpoint zero and constant at endpoint
one. -/
def rightCommaArrowNerveHomotopy (F : C ⥤ D) (d : D) :
    SSet.Homotopy
      (nerveMapCommonHom.{u, max v w, 0}
        (rightCommaProjectionFunctor.{u, v, w} F d ⋙ F))
      (nerveMapCommonHom.{u, max v w, 0}
        ((Functor.const ((CostructuredArrow.functor F).obj d : Type (max u v w))).obj d)) :=
  CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
    (rightCommaArrowNatTrans F d)

/-- The projected right-comma nerve followed by `nerveMap F` is the zero
endpoint of the rowwise comma-arrow homotopy. -/
theorem rightCommaProjection_comp_nerveMap (F : C ⥤ D) (d : D) :
    (rightCommaProjection.{u, v, w} F).app d ≫ nerveMapCommonHom.{u, w, v} F =
      nerveMapCommonHom.{u, max v w, 0}
        (rightCommaProjectionFunctor.{u, v, w} F d ⋙ F) :=
  by
    ext Δ X
    rfl

/-- Endpoint-zero formula for the rowwise comma-arrow homotopy. -/
theorem rightCommaArrowNerveHomotopy_h₀ (F : C ⥤ D) (d : D) :
    SSet.ι₀ ≫ (rightCommaArrowNerveHomotopy F d).h =
      nerveMapCommonHom.{u, max v w, 0}
        (rightCommaProjectionFunctor.{u, v, w} F d ⋙ F) :=
  (rightCommaArrowNerveHomotopy F d).h₀

/-- Endpoint-one formula for the rowwise comma-arrow homotopy. -/
theorem rightCommaArrowNerveHomotopy_h₁ (F : C ⥤ D) (d : D) :
    SSet.ι₁ ≫ (rightCommaArrowNerveHomotopy F d).h =
      nerveMapCommonHom.{u, max v w, 0}
        ((Functor.const ((CostructuredArrow.functor F).obj d : Type (max u v w))).obj d) :=
  (rightCommaArrowNerveHomotopy F d).h₁

end SSet

end


noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v w

namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

private theorem originalRightCommaArrowNerveHomotopyHValueComputed
    (F : C ⥤ D) (d : D) :
    (rightCommaArrowNerveHomotopy.{u, v, w} F d).h =
      (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTrans.{u, v, w} F d)).h := rfl

/-- The whole h field is the SAME original common-Hom right-comma cylinder. -/
public theorem rightCommaArrowNerveHomotopy_h_value
    (F : C ⥤ D) (d : D) :
    (rightCommaArrowNerveHomotopy.{u, v, w} F d).h =
      (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTrans.{u, v, w} F d)).h :=
  originalRightCommaArrowNerveHomotopyHValueComputed F d

end SSet

end
