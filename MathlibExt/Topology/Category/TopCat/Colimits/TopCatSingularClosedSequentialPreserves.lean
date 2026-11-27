/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import
  MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedSequentialColimit
/-!
# Singular complexes of closed T1 sequential colimits

For a natural-number chain F with closed T1-embedding transition maps, each singular simplex of
a colimit comes from a stage and the singular maps of the stage legs are injective. These facts
make the degreewise singular cocones colimiting, so the singular-complex functor preserves
colimits of F.

An injective continuous map also induces injective maps in all singular degrees. A closed
T1-embedding is a closed embedding whose codomain singleton is closed at every point outside the
image. The ambient universe u is arbitrary.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

/-- For a continuous map f:X→Y with injective underlying function, the induced map on singular
simplices is injective in every simplicial degree. -/
theorem injective_toSSet_map_app_of_injective
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : Function.Injective f.hom) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((toSSet.map f).app n) := by
  intro a b hab
  have hNat (z : (toSSet.obj X).obj n) :
      (toSSetObjEquiv Y n) ((toSSet.map f).app n z) =
        f.hom.comp ((toSSetObjEquiv X n) z) := by
    conv_lhs => rw [← Equiv.symm_apply_apply (toSSetObjEquiv X n) z]
    have hRfl :
        (toSSetObjEquiv Y n) ((toSSet.map f).app n
          ((toSSetObjEquiv X n).symm ((toSSetObjEquiv X n) z))) =
          f.hom.comp ((toSSetObjEquiv X n)
            ((toSSetObjEquiv X n).symm ((toSSetObjEquiv X n) z))) :=
      rfl
    rw [Equiv.apply_symm_apply] at hRfl
    exact hRfl
  have hEq : f.hom.comp ((toSSetObjEquiv X n) a) =
      f.hom.comp ((toSSetObjEquiv X n) b) := by
    rw [← hNat a, ← hNat b, hab]
  have hPt (t : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
      ((toSSetObjEquiv X n) a) t = ((toSSetObjEquiv X n) b) t := by
    have h1 := ContinuousMap.congr_fun hEq t
    simpa using hf h1
  have hCont : (toSSetObjEquiv X n) a = (toSSetObjEquiv X n) b :=
    ContinuousMap.ext fun t => hPt t
  exact (toSSetObjEquiv X n).injective hCont

/-- Let F:ℕ→TopCat.{u} be a chain whose every transition map is a closed embedding with closed
codomain singletons outside its image. For a colimiting cocone c, each colimit leg induces an
injective singular-simplex map in every degree. -/
theorem injective_toSSet_leg_app_of_closedT1
    {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    (j : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((toSSet.map (c.ι.app j)).app n) := by
  apply injective_toSSet_map_app_of_injective
  have hFclosed : ∀ ⦃i k : ℕ⦄ (f : i ⟶ k),
      IsClosedEmbedding (F.map f).hom :=
    fun _ _ f => closedT1Embeddings_le_isClosedEmbedding _ (hF f)
  have hLeg : IsClosedEmbedding (c.ι.app j).hom :=
    isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding c hc hFclosed j
  exact hLeg.injective

/-- Let F:ℕ→TopCat.{u} be a chain whose every transition map is a closed embedding with closed
codomain singletons outside its image. The functor taking degree-n singular simplices preserves
colimits of this diagram, for every simplicial degree n. -/
theorem preservesColimit_comp_evaluation_of_closedT1
    {F : ℕ ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) :
    PreservesColimit F
      (toSSet ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n) := by
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?hsurj ?hinj⟩
  case hsurj =>
    intro x
    obtain ⟨j, y, hy⟩ := toSSet_stage_exists c hc hF n x
    exact ⟨j, y, by simpa using hy.symm⟩
  case hinj =>
    intro i x y hxy
    have hInj :
        Function.Injective
          (((toSSet ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCocone
            c).ι.app i) := by
      have hSSet :=
        injective_toSSet_leg_app_of_closedT1 c hc hF i n
      simpa using hSSet
    have hEq : x = y := hInj hxy
    exact ⟨i, 𝟙 i, by simpa using hEq⟩

/-- Let F:ℕ→TopCat.{u} be a chain whose every transition map is a closed embedding with closed
codomain singletons outside its image. The singular-complex functor sends every colimiting
cocone of F to a colimiting simplicial-set cocone. -/
theorem preservesColimit_toSSet_of_closedT1
    {F : ℕ ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), closedT1Embeddings (F.map f)) :
    PreservesColimit F toSSet :=
  preservesColimit_of_evaluation _ _ fun n =>
    preservesColimit_comp_evaluation_of_closedT1 hF n

end TopCat
