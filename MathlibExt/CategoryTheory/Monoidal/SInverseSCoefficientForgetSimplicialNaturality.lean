/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetObjectNaturality

/-!
# Naturality of forgotten coefficient-bar data and simplicial objects

The degreewise forgetful coefficient-bar comparison is natural in the
coefficient system.  Extensionality promotes that square to simplicial data,
and the canonical postcomposition/data-mapping comparison transports it to
genuine simplicial coefficient bars.

This file does not pass to alternating or normalized complexes, homology, or
localization comparisons.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace CategoryTheory
namespace SInverseS

variable {J A : Type u} [Category.{u} J] [CommRing A]
  {M N : J ⥤ ModuleCat.{u} A}


/-- The coefficient-bar data forgetful comparison is natural in the
coefficient system. -/
theorem coefficientBarForgetDataIso_hom_naturality
    (α : M ⟶ N) :
    (SimplicialObject.Data.mapFunctor (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map
          (CategoryHomology.coefficientBarDataMap α) ≫
        (coefficientBarForgetDataIso N).hom =
      (coefficientBarForgetDataIso M).hom ≫
        CategoryHomology.coefficientBarDataMap
          (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) := by
  apply SimplicialObject.Data.Hom.ext
  intro k
  change
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarMap α k) ≫
        (coefficientBarForgetObjIso N k).hom =
      (coefficientBarForgetObjIso M k).hom ≫
        CategoryHomology.coefficientBarMap
          (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) k
  exact coefficientBarForgetObjIso_hom_naturality α k

/-- The genuine simplicial coefficient-bar forgetful comparison is natural
in the coefficient system. -/
theorem coefficientBarForgetSimplicialIso_hom_naturality
    (α : M ⟶ N) :
    Functor.whiskerRight
          (CategoryHomology.coefficientBarSimplicialMap α) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≫
        (coefficientBarForgetSimplicialIso N).hom =
      (coefficientBarForgetSimplicialIso M).hom ≫
        CategoryHomology.coefficientBarSimplicialMap
          (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) := by
  let G := SimplicialObject.Data.toSimplicialFunctor
    (C := AddCommGrpCat.{u})
  let bM :=
    (SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app
      (CategoryHomology.coefficientBarData M)
  let bN :=
    (SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app
      (CategoryHomology.coefficientBarData N)
  let dM := coefficientBarForgetDataIso M
  let dN := coefficientBarForgetDataIso N
  have hBridge :=
    (SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).hom.naturality
      (CategoryHomology.coefficientBarDataMap α)
  change Functor.whiskerRight
        (CategoryHomology.coefficientBarSimplicialMap α) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≫
      bN.hom = bM.hom ≫
        G.map ((SimplicialObject.Data.mapFunctor (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map
          (CategoryHomology.coefficientBarDataMap α)) at hBridge
  have hData := congrArg G.map
    (coefficientBarForgetDataIso_hom_naturality α)
  rw [G.map_comp, G.map_comp] at hData
  change G.map ((SimplicialObject.Data.mapFunctor (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map
        (CategoryHomology.coefficientBarDataMap α)) ≫
      (G.mapIso dN).hom =
    (G.mapIso dM).hom ≫
      CategoryHomology.coefficientBarSimplicialMap
        (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) at hData
  change Functor.whiskerRight
        (CategoryHomology.coefficientBarSimplicialMap α) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≫
      (bN.hom ≫ (G.mapIso dN).hom) =
    (bM.hom ≫ (G.mapIso dM).hom) ≫
      CategoryHomology.coefficientBarSimplicialMap
        (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
  calc
    _ = (Functor.whiskerRight
          (CategoryHomology.coefficientBarSimplicialMap α) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≫
          bN.hom) ≫ (G.mapIso dN).hom :=
      (Category.assoc _ _ _).symm
    _ = (bM.hom ≫ G.map
          ((SimplicialObject.Data.mapFunctor (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map
            (CategoryHomology.coefficientBarDataMap α))) ≫
        (G.mapIso dN).hom := by rw [hBridge]
    _ = bM.hom ≫
        (G.map ((SimplicialObject.Data.mapFunctor (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map
            (CategoryHomology.coefficientBarDataMap α)) ≫
          (G.mapIso dN).hom) := Category.assoc _ _ _
    _ = bM.hom ≫
        ((G.mapIso dM).hom ≫
          CategoryHomology.coefficientBarSimplicialMap
            (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))) := by rw [hData]
    _ = (bM.hom ≫ (G.mapIso dM).hom) ≫
        CategoryHomology.coefficientBarSimplicialMap
          (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
      (Category.assoc _ _ _).symm

end SInverseS
end CategoryTheory

end
