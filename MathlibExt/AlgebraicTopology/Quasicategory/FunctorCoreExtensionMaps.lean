/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreExtensionSpaces
import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreKanProbe
import MathlibExt.CategoryTheory.Limits.Shapes.PullbackFibreBaseChange

/-!
# Whole original source-pair, target and coefficient actions on extension spaces

Both functor coordinates use the existing contravariant/covariant mapBoth.
The original square and coefficient-family equality determine the actual
pullback map. Its full projections, composition and prism action are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.FunctorCore.Extension

variable {A₀ A B₀ B Q Q' K L : SSet.{u}}

/-- The original source square gives the full existing functor-core restriction square. -/
theorem restriction_square (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j) :
    restriction j Q ≫ FunctorCore.mapBoth u₀ g =
      FunctorCore.mapBoth u₁ g ≫ restriction i Q' := by
  have hp : (FunctorCore.sourceMap j).app Q ≫ (FunctorCore.sourceMap u₀).app Q =
      (FunctorCore.sourceMap u₁).app Q ≫ (FunctorCore.sourceMap i).app Q := by
    have hn := NatTrans.congr_app (congrArg FunctorCore.sourceMap h) Q
    simpa only [FunctorCore.sourceMap_comp, NatTrans.comp_app] using hn.symm
  change (FunctorCore.sourceMap j).app Q ≫ FunctorCore.mapBoth u₀ g =
    FunctorCore.mapBoth u₁ g ≫ (FunctorCore.sourceMap i).app Q'
  rw [FunctorCore.mapBoth, FunctorCore.mapBoth]
  calc
    _ = ((FunctorCore.sourceMap j).app Q ≫ (FunctorCore.sourceMap u₀).app Q) ≫
        (FunctorCore.functor A₀).map g := (Category.assoc _ _ _).symm
    _ = ((FunctorCore.sourceMap u₁).app Q ≫ (FunctorCore.sourceMap i).app Q) ≫
        (FunctorCore.functor A₀).map g := by rw [hp]
    _ = _ := by rw [Category.assoc, ← FunctorCore.sourceMap_natural i g, ← Category.assoc]

/-- The actual combined action retains both original functor maps and coefficient map. -/
def map (i : A₀ ⟶ A) (j : B₀ ⟶ B) (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B)
    (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β) : object j α ⟶ object i β :=
  pullback.map (restriction j Q) α (restriction i Q') β
    (FunctorCore.mapBoth u₁ g) c (FunctorCore.mapBoth u₀ g)
    (restriction_square i j u₀ u₁ g h) hc

/-- The entire original functor-coordinate action is the same native mapBoth. -/
@[reassoc]
theorem map_fst (i : A₀ ⟶ A) (j : B₀ ⟶ B) (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B)
    (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β) :
    map i j u₀ u₁ g h α β c hc ≫ functorProjection i β =
      functorProjection j α ≫ FunctorCore.mapBoth u₁ g := pullback.lift_fst _ _ _

/-- The entire original coefficient-coordinate action retains the prescribed coefficient map. -/
@[reassoc]
theorem map_snd (i : A₀ ⟶ A) (j : B₀ ⟶ B) (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B)
    (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β) :
    map i j u₀ u₁ g h α β c hc ≫ coefficientProjection i β =
      coefficientProjection j α ≫ c := pullback.lift_snd _ _ _

/-- Identity retains the actual original extension object and both projections. -/
theorem map_id (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    map i i (𝟙 A₀) (𝟙 A) (𝟙 Q) (by simp) α α (𝟙 K)
      (by rw [FunctorCore.mapBoth_id, Category.comp_id, Category.id_comp]) = 𝟙 (object i α) := by
  apply pullback.hom_ext
  · rw [map_fst, FunctorCore.mapBoth_id, Category.comp_id, Category.id_comp]
  · rw [map_snd, Category.comp_id, Category.id_comp]

/-- Actual compatible source squares compose in the original contravariant order. -/
theorem square_comp {C₀ C : SSet.{u}} (i : A₀ ⟶ A) (j : B₀ ⟶ B) (k : C₀ ⟶ C)
    (u₀ : B₀ ⟶ C₀) (u₁ : B ⟶ C) (hu : j ≫ u₁ = u₀ ≫ k)
    (v₀ : A₀ ⟶ B₀) (v₁ : A ⟶ B) (hv : i ≫ v₁ = v₀ ≫ j) :
    i ≫ (v₁ ≫ u₁) = (v₀ ≫ u₀) ≫ k := by
  rw [← Category.assoc, hv, Category.assoc, hu, ← Category.assoc]

/-- Actual coefficient-family squares compose with the same mapBoth formula. -/
theorem family_comp {C₀ Q'' M : SSet.{u}} (u₀ : B₀ ⟶ C₀) (v₀ : A₀ ⟶ B₀)
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'')
    (α : K ⟶ (FunctorCore.functor C₀).obj Q)
    (β : L ⟶ (FunctorCore.functor B₀).obj Q')
    (γ : M ⟶ (FunctorCore.functor A₀).obj Q'') (c : K ⟶ L) (d : L ⟶ M)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (hd : β ≫ FunctorCore.mapBoth v₀ g' = d ≫ γ) :
    α ≫ FunctorCore.mapBoth (v₀ ≫ u₀) (g ≫ g') = (c ≫ d) ≫ γ := by
  rw [← FunctorCore.mapBoth_comp v₀ u₀ g g', ← Category.assoc, hc,
    Category.assoc, hd, ← Category.assoc]

/-- The actual complete pullback actions compose, preserving both original coordinates. -/
theorem map_comp {C₀ C Q'' M : SSet.{u}} (i : A₀ ⟶ A) (j : B₀ ⟶ B) (k : C₀ ⟶ C)
    (u₀ : B₀ ⟶ C₀) (u₁ : B ⟶ C) (hu : j ≫ u₁ = u₀ ≫ k)
    (v₀ : A₀ ⟶ B₀) (v₁ : A ⟶ B) (hv : i ≫ v₁ = v₀ ≫ j)
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'')
    (α : K ⟶ (FunctorCore.functor C₀).obj Q)
    (β : L ⟶ (FunctorCore.functor B₀).obj Q')
    (γ : M ⟶ (FunctorCore.functor A₀).obj Q'') (c : K ⟶ L) (d : L ⟶ M)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (hd : β ≫ FunctorCore.mapBoth v₀ g' = d ≫ γ) :
    map j k u₀ u₁ g hu α β c hc ≫ map i j v₀ v₁ g' hv β γ d hd =
      map i k (v₀ ≫ u₀) (v₁ ≫ u₁) (g ≫ g')
        (square_comp i j k u₀ u₁ hu v₀ v₁ hv) α γ (c ≫ d)
        (family_comp u₀ v₀ g g' α β γ c d hc hd) := by
  apply pullback.hom_ext
  · rw [Category.assoc, map_fst, ← Category.assoc, map_fst, Category.assoc,
      FunctorCore.mapBoth_comp, map_fst]
  · rw [Category.assoc, map_snd, ← Category.assoc, map_snd, Category.assoc, map_snd]

/-- The same-coefficient original action is literally the canonical sharp-fibre map. -/
theorem map_sameCoefficient (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) :
    map i j u₀ u₁ g h α (α ≫ FunctorCore.mapBoth u₀ g) (𝟙 K) (by simp) =
      HomotopicalAlgebra.SharpFibreMapWeak.fibreMap (restriction j Q) (restriction i Q')
        (FunctorCore.mapBoth u₁ g) (FunctorCore.mapBoth u₀ g)
        (restriction_square i j u₀ u₁ g h).symm α := rfl

/-- The original whole prism action is precomposition followed by the actual target map. -/
theorem prism_map {T : SSet.{u}} (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β) (f : T ⟶ object j α) :
    prism i β (f ≫ map i j u₀ u₁ g h α β c hc) = u₁ ▷ T ≫ prism j α f ≫ g := by
  apply curry_injective
  rw [← Category.assoc, curry_natural_right, ← curry_pre_app, prism_curry, prism_curry]
  simp only [Category.assoc]
  rw [map_fst_assoc, FunctorCore.mapBoth_inclusion]

end SSet.FunctorCore.Extension
