/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.NerveData

/-!
# Generic nerve-data public contract

Focused flat-namespace pins for the generic nerve simplicial data relocated from
`CategoryTheory.CategoryBar.NerveComparison`, following the flat `CategoryTheory`
precedent of `NerveHomotopy.lean`.

Compile-level consumers for `CategoryTheory.nerveData`, `nerveData_δ`,
`nerveData_σ`, and `nerveDataSimplicialIso`, moved from
`CategoryBar/NerveComparisonTests.lean` to this flat module.
-/

open CategoryTheory Opposite

universe u v

namespace MathlibExtTest.CategoryTheory.NerveDataTests

variable {C : Type u} [Category.{v} C]

noncomputable example : SimplicialObject.Data (Type (max u v)) :=
  CategoryTheory.nerveData C

example {n : ℕ} (i : Fin (n + 2)) :
    (CategoryTheory.nerveData C).δ i =
      (nerve C).map (SimplexCategory.δ i).op :=
  CategoryTheory.nerveData_δ i

example {n : ℕ} (i : Fin (n + 1)) :
    (CategoryTheory.nerveData C).σ i =
      (nerve C).map (SimplexCategory.σ i).op :=
  CategoryTheory.nerveData_σ i

noncomputable example : (CategoryTheory.nerveData C).toSimplicialObject ≅ nerve C :=
  CategoryTheory.nerveDataSimplicialIso C

example (n : ℕ) :
    (CategoryTheory.nerveDataSimplicialIso C).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      𝟙 (ComposableArrows C n) :=
  CategoryTheory.nerveDataSimplicialIso_hom_app n

example (n : ℕ) :
    (CategoryTheory.nerveDataSimplicialIso C).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      𝟙 (ComposableArrows C n) :=
  CategoryTheory.nerveDataSimplicialIso_inv_app n

end MathlibExtTest.CategoryTheory.NerveDataTests
