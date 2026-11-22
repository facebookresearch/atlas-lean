/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreExtensionMaps
import MathlibExt.AlgebraicTopology.ModelCategory.SharpFibreMapWeak
import MathlibExt.AlgebraicTopology.ModelCategory.SharpFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Genuine weak comparisons of the original functor-extension spaces

Original categorical equivalences supply the two full functor-core weak maps.
The canonical sharp-fibre theorem proves their literal extension comparison
weak. Coefficient change uses the actual native over-pullback along the original
restriction fibration. No fibre weakness or comparison preservation is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FunctorCore.Extension

variable {A₀ A B₀ B Q Q' K L : SSet.{u}}

/-- The actual same-coefficient extension map is weak from the three original categorical equivalences. -/
theorem map_sameCoefficient_realizationWeak (i : A₀ ⟶ A) [Mono i]
    (j : B₀ ⟶ B) [Mono j] [Quasicategory Q] [Quasicategory Q']
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (hu₀ : categoricalEquivalences u₀) (hu₁ : categoricalEquivalences u₁)
    (hg : categoricalEquivalences g) (α : K ⟶ (FunctorCore.functor B₀).obj Q) :
    realizationWeakEquivalences
      (map i j u₀ u₁ g h α (α ≫ FunctorCore.mapBoth u₀ g) (𝟙 K) (by simp)) := by
  rw [map_sameCoefficient]
  exact SharpFibreMapWeak.fibreMap_weak (restriction j Q) (restriction i Q')
    (FunctorCore.mapBoth u₁ g) (FunctorCore.mapBoth u₀ g)
    (restriction_square i j u₀ u₁ g h).symm α
    (sharpMaps_of_fibration _) (sharpMaps_of_fibration _)
    (FunctorCore.mapBoth_realizationWeak u₁ g hu₁ hg)
    (FunctorCore.mapBoth_realizationWeak u₀ g hu₀ hg)

/-- The actual original coefficient change is the chosen pullback map with both functor coordinates fixed. -/
def coefficientMap (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q) (c : K ⟶ L) (hc : α = c ≫ β) :
    object i α ⟶ object i β :=
  pullback.map (restriction i Q) α (restriction i Q) β (𝟙 _) c (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using hc)

/-- Coefficient change retains the original whole functor coordinate. -/
@[reassoc]
theorem coefficientMap_fst (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q) (c : K ⟶ L) (hc : α = c ≫ β) :
    coefficientMap i α β c hc ≫ functorProjection i β = functorProjection i α := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- Coefficient change retains the actual prescribed coefficient map. -/
@[reassoc]
theorem coefficientMap_snd (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q) (c : K ⟶ L) (hc : α = c ≫ β) :
    coefficientMap i α β c hc ≫ coefficientProjection i β = coefficientProjection i α ≫ c :=
  pullback.lift_snd _ _ _

/-- The actual coefficient map is the same native over-pullback map in the chosen pullback order. -/
theorem coefficientMap_eq_overPullback (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q) (c : K ⟶ L) (hc : α = c ≫ β) :
    coefficientMap i α β c hc =
      (pullbackSymmetry (restriction i Q) α).hom ≫
        ((Over.pullback (restriction i Q)).map (Over.homMk c hc.symm : Over.mk α ⟶ Over.mk β)).left ≫
          (pullbackSymmetry (restriction i Q) β).inv := by
  apply pullback.hom_ext
  · rw [coefficientMap_fst]
    symm
    simp only [Category.assoc, pullbackSymmetry_inv_comp_fst, Over.pullback_map_left,
      Over.mk, Over.homMk, Over.hom, Over.Hom.left, CostructuredArrow.mk,
      CostructuredArrow.homMk]
    rw [pullback.lift_snd, pullbackSymmetry_hom_comp_snd]
  · rw [coefficientMap_snd]
    symm
    simp only [Category.assoc, pullbackSymmetry_inv_comp_snd, Over.pullback_map_left,
      Over.mk, Over.homMk, Over.hom, Over.Hom.left, CostructuredArrow.mk,
      CostructuredArrow.homMk]
    rw [pullback.lift_fst, ← Category.assoc, pullbackSymmetry_hom_comp_fst]

/-- An actual original weak coefficient map gives a weak extension map along the original restriction fibration. -/
theorem coefficientMap_realizationWeak (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q) (c : K ⟶ L) (hc : α = c ≫ β)
    (hWeak : realizationWeakEquivalences c) :
    realizationWeakEquivalences (coefficientMap i α β c hc) := by
  rw [coefficientMap_eq_overPullback]
  let f : Over.mk α ⟶ Over.mk β := Over.homMk c hc.symm
  have h : realizationWeakEquivalences ((Over.pullback (restriction i Q)).map f).left :=
    MorphismProperty.sharpMaps_pullback_map (weakEquivalences SSet.{u})
      (sharpMaps_of_fibration (restriction i Q)) f hWeak
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) (realizationWeakEquivalences.comp_mem _ _ h
      (realizationWeakEquivalences.of_isIso _))

/-- The original full action factors through the canonical same-coefficient map and actual coefficient change. -/
theorem map_factor_coefficient (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β) :
    map i j u₀ u₁ g h α β c hc =
      map i j u₀ u₁ g h α (α ≫ FunctorCore.mapBoth u₀ g) (𝟙 K) (by simp) ≫
        coefficientMap i (α ≫ FunctorCore.mapBoth u₀ g) β c hc := by
  apply pullback.hom_ext
  · rw [map_fst, Category.assoc, coefficientMap_fst, map_fst]
  · rw [map_snd, Category.assoc, coefficientMap_snd, ← Category.assoc, map_snd,
      Category.comp_id]

/-- The same complete original map is weak from genuine source-pair, target and coefficient weakness. -/
theorem map_realizationWeak (i : A₀ ⟶ A) [Mono i] (j : B₀ ⟶ B) [Mono j]
    [Quasicategory Q] [Quasicategory Q']
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (hu₀ : categoricalEquivalences u₀) (hu₁ : categoricalEquivalences u₁)
    (hg : categoricalEquivalences g)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β) (hWeak : realizationWeakEquivalences c) :
    realizationWeakEquivalences (map i j u₀ u₁ g h α β c hc) := by
  rw [map_factor_coefficient]
  exact realizationWeakEquivalences.comp_mem _ _
    (map_sameCoefficient_realizationWeak i j u₀ u₁ g h hu₀ hu₁ hg α)
    (coefficientMap_realizationWeak i _ β c hc hWeak)

/-- For genuine Kan coefficients the original complete weak comparison is a Kan weak map. -/
theorem map_weak (i : A₀ ⟶ A) [Mono i] (j : B₀ ⟶ B) [Mono j]
    [Quasicategory Q] [Quasicategory Q'] [KanComplex K] [KanComplex L]
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (hu₀ : categoricalEquivalences u₀) (hu₁ : categoricalEquivalences u₁)
    (hg : categoricalEquivalences g)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β) (hWeak : KanComplex.W c) :
    KanComplex.W (map i j u₀ u₁ g h α β c hc) := by
  let _ : KanComplex (object j α) := object_isKan j α
  let _ : KanComplex (object i β) := object_isKan i β
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (map_realizationWeak i j u₀ u₁ g h hu₀ hu₁ hg α β c hc
      ((KanComplex.W_iff_realizationWeakEquivalence c).mp hWeak))

end SSet.FunctorCore.Extension
