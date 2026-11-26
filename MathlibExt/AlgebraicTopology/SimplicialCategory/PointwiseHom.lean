/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Pointwise mapping objects for simplicial spaces

For simplicial objects in simplicial sets, this file selects the
`SSet`-valued enriched end of the inner internal-Hom objects. This is the
pointwise mapping simplicial set: its simplicial direction is the inner one.
It is distinct from the canonical outer `SimplicialCategory.sHom` on the
functor category.

The closed-self enrichment and all required ends are selected only inside
the definitions and proofs below. No second global enrichment or closed
instance is installed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite

namespace SSet

/-- The `SSet`-valued end of the inner mapping objects of two simplicial
spaces. -/
noncomputable def simplicialSpacePointwiseHom :
    (SimplicialObject SSet.{u})ᵒᵖ ⥤
      SimplicialObject SSet.{u} ⥤ SSet.{u} := by
  letI : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  letI : ∀ (X Y : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} X Y :=
    inferInstance
  let pointwiseOrdinary : EnrichedOrdinaryCategory SSet.{u}
      (SimplicialObject SSet.{u}) :=
    Enriched.FunctorCategory.enrichedOrdinaryCategory
      SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
  letI : EnrichedCategory SSet.{u} (SimplicialObject SSet.{u}) :=
    pointwiseOrdinary.toEnrichedCategory
  letI : EnrichedOrdinaryCategory SSet.{u}
      (SimplicialObject SSet.{u}) := pointwiseOrdinary
  exact eHomFunctor SSet.{u} (SimplicialObject SSet.{u})

/-- Projection from the pointwise mapping object to the inner mapping object
in one outer degree. -/
noncomputable def simplicialSpacePointwiseHomπ
    (X Y : SimplicialObject SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    ((simplicialSpacePointwiseHom.obj (op X)).obj Y) ⟶
      (ihom (X.obj j)).obj (Y.obj j) := by
  letI : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  letI : ∀ (A B : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} A B :=
    inferInstance
  change Enriched.FunctorCategory.enrichedHom SSet.{u} X Y ⟶ _
  exact Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j

/-- The outer end equation for the pointwise mapping object. -/
theorem simplicialSpacePointwiseHomπ_outer
    (X Y : SimplicialObject SSet.{u}) {i j : SimplexCategoryᵒᵖ}
    (f : i ⟶ j) :
    simplicialSpacePointwiseHomπ X Y i ≫
        (ihom (X.obj i)).map (Y.map f) =
      simplicialSpacePointwiseHomπ X Y j ≫
        (pre (X.map f)).app (Y.obj j) := by
  let _ : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  let hEnds : ∀ (A B : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} A B :=
    inferInstance
  let _ := hEnds
  unfold simplicialSpacePointwiseHomπ
  change Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y i ≫
      (ihom (X.obj i)).map (Y.map f) =
    Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j ≫
      (pre (X.map f)).app (Y.obj j)
  simpa only [
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] using
    Enriched.FunctorCategory.enrichedHom_condition SSet.{u} X Y f

/-- Maps into the pointwise mapping object are equal when all their outer
end projections agree. -/
theorem simplicialSpacePointwiseHom_hom_ext
    (X Y : SimplicialObject SSet.{u}) {Z : SSet.{u}}
    {f g : Z ⟶ (simplicialSpacePointwiseHom.obj (op X)).obj Y}
    (h : ∀ j, f ≫ simplicialSpacePointwiseHomπ X Y j =
      g ≫ simplicialSpacePointwiseHomπ X Y j) : f = g := by
  let _ : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  let hEnds : ∀ (A B : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} A B :=
    inferInstance
  let _ := hEnds
  apply end_.hom_ext
  intro j
  change f ≫ Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j =
    g ≫ Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j
  simpa [simplicialSpacePointwiseHomπ,
    MonoidalClosed.enrichedCategorySelf_hom, _root_.id] using h j

set_option linter.style.haveILetI false in
/-- The projection formula for contravariance in the source simplicial
space. -/
theorem simplicialSpacePointwiseHomπ_map_source
    {X' X : SimplicialObject SSet.{u}} (g : X' ⟶ X)
    (Y : SimplicialObject SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    ((simplicialSpacePointwiseHom.map (op g)).app Y) ≫
        simplicialSpacePointwiseHomπ X' Y j =
      simplicialSpacePointwiseHomπ X Y j ≫
        (pre (g.app j)).app (Y.obj j) := by
  letI : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  letI hEnds : ∀ (A B : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} A B :=
    inferInstance
  let pointwiseOrdinary : EnrichedOrdinaryCategory SSet.{u}
      (SimplicialObject SSet.{u}) :=
    Enriched.FunctorCategory.enrichedOrdinaryCategory
      SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
  letI : EnrichedCategory SSet.{u} (SimplicialObject SSet.{u}) :=
    pointwiseOrdinary.toEnrichedCategory
  letI : EnrichedOrdinaryCategory SSet.{u}
      (SimplicialObject SSet.{u}) := pointwiseOrdinary
  unfold simplicialSpacePointwiseHom simplicialSpacePointwiseHomπ
  let preMap := @eHomWhiskerRight SSet.{u} _ _
    (SimplicialObject SSet.{u}) _ pointwiseOrdinary X' X g Y
  change preMap ≫
      Enriched.FunctorCategory.enrichedHomπ SSet.{u} X' Y j =
    Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j ≫
      (pre (g.app j)).app (Y.obj j)
  dsimp only [preMap, eHomWhiskerRight]
  let comp := @Enriched.FunctorCategory.enrichedComp
    SSet.{u} _ _ SSet.{u} _ SimplexCategoryᵒᵖ _
    (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
    X' X Y (hEnds X' X) (hEnds X Y) (hEnds X' Y)
  have hcomp : @eComp SSet.{u} _ _ (SimplicialObject SSet.{u})
      pointwiseOrdinary.toEnrichedCategory X' X Y = comp := rfl
  rw [hcomp, Category.assoc, Category.assoc]
  dsimp only [comp]
  have hπraw := @Enriched.FunctorCategory.enrichedComp_π
    SSet.{u} _ _ SSet.{u} _ SimplexCategoryᵒᵖ _
    (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
    X' X Y (hEnds X' X) (hEnds X Y) (hEnds X' Y) j
  erw [hπraw]
  let HXY := Enriched.FunctorCategory.enrichedHom SSet.{u} X Y
  let πX'Y := Enriched.FunctorCategory.enrichedHomπ SSet.{u} X' Y j
  let πXY := Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j
  let πX'X := Enriched.FunctorCategory.enrichedHomπ SSet.{u} X' X j
  let hg := Enriched.FunctorCategory.homEquiv SSet.{u} g
  have hg_π : hg ≫ πX'X = (eHomEquiv SSet.{u}) (g.app j) := by
    exact Enriched.FunctorCategory.homEquiv_apply_π SSet.{u} g j
  have hcombine :
      (hg ▷ HXY) ≫ (πX'X ⊗ₘ πXY) =
        (hg ≫ πX'X) ⊗ₘ πXY :=
    MonoidalCategory.whiskerRight_comp_tensorHom _ _ _
  let cbase := eComp SSet.{u} (X'.obj j) (X.obj j) (Y.obj j)
  change (λ_ HXY).inv ≫ (hg ▷ HXY) ≫
      ((πX'X ⊗ₘ πXY) ≫ cbase) = _
  slice_lhs 2 3 => rw [hcombine]
  rw [hg_π]
  have hunit :
      (λ_ HXY).inv ≫ ((eHomEquiv SSet.{u}) (g.app j) ⊗ₘ πXY) =
        πXY ≫ (λ_ _).inv ≫
          (eHomEquiv SSet.{u}) (g.app j) ▷ _ :=
    MonoidalCategory.leftUnitor_inv_comp_tensorHom _ _
  calc
    _ = ((λ_ HXY).inv ≫
        ((eHomEquiv SSet.{u}) (g.app j) ⊗ₘ πXY)) ≫ cbase :=
      (Category.assoc _ _ _).symm
    _ = (πXY ≫ (λ_ _).inv ≫
        (eHomEquiv SSet.{u}) (g.app j) ▷ _) ≫ cbase :=
      hunit =≫ cbase
    _ = _ := by
      rw [← MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      rfl

set_option linter.style.haveILetI false in
/-- The projection formula for covariance in the target simplicial space. -/
theorem simplicialSpacePointwiseHomπ_map_target
    (X : SimplicialObject SSet.{u}) {Y Y' : SimplicialObject SSet.{u}}
    (q : Y ⟶ Y') (j : SimplexCategoryᵒᵖ) :
    ((simplicialSpacePointwiseHom.obj (op X)).map q) ≫
        simplicialSpacePointwiseHomπ X Y' j =
      simplicialSpacePointwiseHomπ X Y j ≫
        (ihom (X.obj j)).map (q.app j) := by
  letI : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  letI hEnds : ∀ (A B : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} A B :=
    inferInstance
  let pointwiseOrdinary : EnrichedOrdinaryCategory SSet.{u}
      (SimplicialObject SSet.{u}) :=
    Enriched.FunctorCategory.enrichedOrdinaryCategory
      SSet.{u} SSet.{u} SimplexCategoryᵒᵖ
  letI : EnrichedCategory SSet.{u} (SimplicialObject SSet.{u}) :=
    pointwiseOrdinary.toEnrichedCategory
  letI : EnrichedOrdinaryCategory SSet.{u}
      (SimplicialObject SSet.{u}) := pointwiseOrdinary
  unfold simplicialSpacePointwiseHom simplicialSpacePointwiseHomπ
  let post := @eHomWhiskerLeft SSet.{u} _ _
    (SimplicialObject SSet.{u}) _ pointwiseOrdinary X Y Y' q
  change post ≫
      Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y' j =
    Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j ≫
      (ihom (X.obj j)).map (q.app j)
  dsimp only [post, eHomWhiskerLeft]
  let comp := @Enriched.FunctorCategory.enrichedComp
    SSet.{u} _ _ SSet.{u} _ SimplexCategoryᵒᵖ _
    (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
    X Y Y' (hEnds X Y) (hEnds Y Y') (hEnds X Y')
  have hcomp : @eComp SSet.{u} _ _ (SimplicialObject SSet.{u})
      pointwiseOrdinary.toEnrichedCategory X Y Y' = comp := rfl
  rw [hcomp, Category.assoc, Category.assoc]
  dsimp only [comp]
  have hπraw := @Enriched.FunctorCategory.enrichedComp_π
    SSet.{u} _ _ SSet.{u} _ SimplexCategoryᵒᵖ _
    (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u})
    X Y Y' (hEnds X Y) (hEnds Y Y') (hEnds X Y') j
  erw [hπraw]
  let HXY := Enriched.FunctorCategory.enrichedHom SSet.{u} X Y
  let HYY' := Enriched.FunctorCategory.enrichedHom SSet.{u} Y Y'
  let πXY := Enriched.FunctorCategory.enrichedHomπ SSet.{u} X Y j
  let πYY' := Enriched.FunctorCategory.enrichedHomπ SSet.{u} Y Y' j
  let hq := Enriched.FunctorCategory.homEquiv SSet.{u} q
  have hq_π : hq ≫ πYY' = (eHomEquiv SSet.{u}) (q.app j) := by
    exact Enriched.FunctorCategory.homEquiv_apply_π SSet.{u} q j
  have hcombine :
      (HXY ◁ hq) ≫ (πXY ⊗ₘ πYY') =
        πXY ⊗ₘ (hq ≫ πYY') :=
    MonoidalCategory.whiskerLeft_comp_tensorHom _ _ _
  let cbase := eComp SSet.{u} (X.obj j) (Y.obj j) (Y'.obj j)
  change (ρ_ HXY).inv ≫ (HXY ◁ hq) ≫
      ((πXY ⊗ₘ πYY') ≫ cbase) = _
  slice_lhs 2 3 => rw [hcombine]
  rw [hq_π]
  have hunit :
      (ρ_ HXY).inv ≫ (πXY ⊗ₘ (eHomEquiv SSet.{u}) (q.app j)) =
        πXY ≫ (ρ_ _).inv ≫
          _ ◁ (eHomEquiv SSet.{u}) (q.app j) :=
    MonoidalCategory.rightUnitor_inv_comp_tensorHom _ _
  calc
    _ = ((ρ_ HXY).inv ≫
        (πXY ⊗ₘ (eHomEquiv SSet.{u}) (q.app j))) ≫ cbase :=
      (Category.assoc _ _ _).symm
    _ = (πXY ≫ (ρ_ _).inv ≫
        _ ◁ (eHomEquiv SSet.{u}) (q.app j)) ≫ cbase :=
      hunit =≫ cbase
    _ = _ := by
      rw [← MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
      simp only [Category.assoc]
      rfl

end SSet

end
