/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NerveHomotopy

/-! # Nerve prisms and chain functors: tests

These tests exercise the nerve-prism API of the neutral module
`MathlibExt.CategoryTheory.NerveHomotopy`:
`CategoryTheory.Functor.nervePrismMap` with its value and face
formulas, the chain functor `CategoryTheory.NatTrans.nerveChainFunctor`
with its three faces, and the identity computations
`CategoryTheory.NatTrans.nerveCylinderFunctor_id` and
`CategoryTheory.Functor.nervePrismMap_fst_comp`. They deliberately
import only the neutral module, not the Joyal theory that consumes it
(`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.NerveGate`).
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial CategoryTheory.Prod

universe u v

namespace MathlibExtTest.CategoryTheory
namespace NervePrismTests

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G H : C ⥤ D}

example (Φ : C × Fin 2 ⥤ D) :
    CategoryTheory.nerve C ⊗ Δ[1] ⟶ CategoryTheory.nerve D :=
  Φ.nervePrismMap

example (Φ : C × Fin 2 ⥤ D) {Δ : SimplexCategoryᵒᵖ}
    (X : (CategoryTheory.nerve C ⊗ Δ[1]).obj Δ) :
    Φ.nervePrismMap.app Δ X =
      (Φ.mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) :=
  CategoryTheory.Functor.nervePrismMap_app Φ X

example (Φ : C × Fin 3 ⥤ D) (i : Fin 3) :
    (CategoryTheory.nerve C ◁ SSet.stdSimplex.δ i) ≫ Φ.nervePrismMap =
      (((𝟭 C).prod (SimplexCategory.δ i).toOrderHom.toFunctor) ⋙
        Φ).nervePrismMap :=
  CategoryTheory.Functor.whiskerLeft_δ_nervePrismMap Φ i

example (α : F ⟶ G) :
    (CategoryTheory.NatTrans.nerveCylinderFunctor α).nervePrismMap =
      CategoryTheory.NatTrans.nerveHomotopyMap α :=
  CategoryTheory.NatTrans.nervePrismMap_nerveCylinderFunctor α

example (α : F ⟶ G) (β : G ⟶ H) : C × Fin 3 ⥤ D :=
  CategoryTheory.NatTrans.nerveChainFunctor α β

example (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFunctor) ⋙
        CategoryTheory.NatTrans.nerveChainFunctor α β =
      CategoryTheory.NatTrans.nerveCylinderFunctor α :=
  CategoryTheory.NatTrans.prod_δ_two_comp_nerveChainFunctor α β

example (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFunctor) ⋙
        CategoryTheory.NatTrans.nerveChainFunctor α β =
      CategoryTheory.NatTrans.nerveCylinderFunctor β :=
  CategoryTheory.NatTrans.prod_δ_zero_comp_nerveChainFunctor α β

example (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFunctor) ⋙
        CategoryTheory.NatTrans.nerveChainFunctor α β =
      CategoryTheory.NatTrans.nerveCylinderFunctor (α ≫ β) :=
  CategoryTheory.NatTrans.prod_δ_one_comp_nerveChainFunctor α β

example :
    CategoryTheory.NatTrans.nerveCylinderFunctor (𝟙 F) =
      CategoryTheory.Prod.fst C (Fin 2) ⋙ F :=
  CategoryTheory.NatTrans.nerveCylinderFunctor_id

example :
    (CategoryTheory.Prod.fst C (Fin 2) ⋙ F).nervePrismMap =
      SemiCartesianMonoidalCategory.fst (CategoryTheory.nerve C)
          (Δ[1] : SSet.{max u v}) ≫ CategoryTheory.nerveMap F :=
  CategoryTheory.Functor.nervePrismMap_fst_comp

end NervePrismTests
end MathlibExtTest.CategoryTheory

end
