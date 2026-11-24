/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryBar.CommaRightPointNaturality

/-!
# Right-comma point-naturality public contract

Compile-level pin for `CategoryBar.barRightComma_naturality_d`.

Nonclaims: no degreewise comparison, no other functor/naturality variant, no
contraction, no homotopy, no realization, and no KQ statement.
-/

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace MathlibExtTest.CategoryBar.CommaRightPointTests

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

example (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    CategoryBar.categoryBarMap (CategoryBar.commaCoeffRMap F g)
        (𝟙 (CategoryBar.unitCoeffL C)) ≫
        (CategoryBar.barRightCommaSimplicialIso F d').hom =
      (CategoryBar.barRightCommaSimplicialIso F d).hom ≫
        nerveMap (CostructuredArrow.map g) :=
  CategoryBar.barRightComma_naturality_d F g

end MathlibExtTest.CategoryBar.CommaRightPointTests
