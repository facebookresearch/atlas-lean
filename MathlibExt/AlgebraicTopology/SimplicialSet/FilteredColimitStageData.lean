/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Model-free original stage geometry.
module
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace SSet.FilteredColimitStage

/-- Original filtered mono diagrams have mono ORIGINAL cocone legs in every simplicial degree. -/
theorem cocone_legs_mono_of_maps_mono
    {J : Type v} [Category.{w} J] [Small.{u} J] [IsFiltered J]
    {F : J ⥤ SSet.{u}} (c : Cocone F) (hc : IsColimit c)
    (hm : ∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (F.map f)) :
    ∀ j, Mono (c.ι.app j) := by
  intro j
  rw [NatTrans.mono_iff_mono_app]
  intro a
  let E : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj a
  have hE : IsColimit (E.mapCocone c) := isColimitOfPreserves E hc
  apply (CategoryTheory.mono_iff_injective ((c.ι.app j).app a)).mpr
  intro x y hxy
  obtain ⟨k, f, h⟩ := (Types.FilteredColimit.isColimit_eq_iff' hE x y).mp hxy
  let _ : Mono (F.map f) := hm f
  exact (CategoryTheory.mono_iff_injective ((F.map f).app a)).mp inferInstance h

/-- A whole represented simplex factors through ONE original stage, chosen before all operators. -/
theorem exists_simplex_stage_with_all_operators
    {J : Type v} [Category.{w} J] [Small.{u} J]
    {F : J ⥤ SSet.{u}} (c : Cocone F) (hc : IsColimit c)
    (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ c.pt) :
    ∃ (j : J) (bj : (Δ[n] : SSet.{u}) ⟶ F.obj j),
      bj ≫ c.ι.app j = b ∧
        ∀ (m : ℕ) (delta : ⦋m⦌ ⟶ ⦋n⦌),
          (SSet.stdSimplex.map delta ≫ bj) ≫ c.ι.app j = SSet.stdSimplex.map delta ≫ b := by
  let E : SSet.{u} ⥤ Type u :=
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌)
  have hE : IsColimit (E.mapCocone c) := isColimitOfPreserves E hc
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hE (SSet.yonedaEquiv b)
  change (c.ι.app j).app (op ⦋n⦌) x = SSet.yonedaEquiv b at hx
  let bj : (Δ[n] : SSet.{u}) ⟶ F.obj j := SSet.yonedaEquiv.symm x
  have hb : bj ≫ c.ι.app j = b := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, bj, Equiv.apply_symm_apply] using hx
  refine ⟨j, bj, hb, ?_⟩
  intro m delta
  rw [Category.assoc, hb]

end SSet.FilteredColimitStage
