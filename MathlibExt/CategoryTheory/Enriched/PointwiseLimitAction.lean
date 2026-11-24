/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Evaluation
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Particular limit actions for genuine enriched functors

The full right Hom action descends into the original evaluated target limit.
No ordinary structure on the enriched source is required.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace CategoryTheory.EnrichedFunctorCat.PointwiseLimit
open Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)

/-- The original source limit projections followed by the complete enriched actions. -/
def actionCone (a b : A) [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)] :
    Cone (K ⋙ EnrichedFunctorCat.evaluation b) where
  pt := limit (K ⋙ EnrichedFunctorCat.evaluation a) ⊗ (a ⟶[V] b)
  π :=
    { app := fun j => (limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      naturality := by
        intro i j f
        let H := a ⟶[V] b
        let L := limit (K ⋙ EnrichedFunctorCat.evaluation a)
        let Xi := (K.obj i).toEnrichedFunctor.obj a
        let Xj := (K.obj j).toEnrichedFunctor.obj a
        let Yi := (K.obj i).toEnrichedFunctor.obj b
        let Yj := (K.obj j).toEnrichedFunctor.obj b
        let pi : L ⟶ Xi := limit.π (K ⋙ EnrichedFunctorCat.evaluation a) i
        let pj : L ⟶ Xj := limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j
        let t : Xi ⟶ Xj := EnrichedFunctorCat.component (K.map f) a
        let m : Yi ⟶ Yj := EnrichedFunctorCat.component (K.map f) b
        let ai : Xi ⊗ H ⟶ Yi := MonoidalClosed.uncurry ((K.obj i).toEnrichedFunctor.map a b)
        let aj : Xj ⊗ H ⟶ Yj := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
        have hn : ai ≫ m = (t ⊗ₘ 𝟙 H) ≫ aj := (K.map f).uncurriedNaturality a b
        have hp : pi ≫ t = pj := limit.w (K ⋙ EnrichedFunctorCat.evaluation a) f
        have hNatural : ai ≫ m = (t ▷ H) ≫ aj := by simpa only [tensorHom_id] using hn
        change 𝟙 (L ⊗ H) ≫ ((pj ▷ H) ≫ aj) = ((pi ▷ H) ≫ ai) ≫ m
        calc
          _ = (pj ▷ H) ≫ aj := Category.id_comp _
          _ = ((pi ≫ t) ▷ H) ≫ aj := by rw [hp]
          _ = (pi ▷ H) ≫ (t ▷ H) ≫ aj := by rw [comp_whiskerRight, Category.assoc]
          _ = _ := by rw [← hNatural, ← Category.assoc] }

/-- The full Hom action maps the original evaluated source limit into the target limit. -/
def action (a b : A)
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation b)] :
    limit (K ⋙ EnrichedFunctorCat.evaluation a) ⊗ (a ⟶[V] b) ⟶
      limit (K ⋙ EnrichedFunctorCat.evaluation b) :=
  limit.lift (K ⋙ EnrichedFunctorCat.evaluation b) (actionCone K a b)

/-- Every original limit projection intertwines the entire enriched Hom action. -/
theorem action_projection (a b : A)
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation b)] (j : J) :
    action K a b ≫ limit.π (K ⋙ EnrichedFunctorCat.evaluation b) j =
      (limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) :=
  limit.lift_π (actionCone K a b) j

/-- The full action is determined by its original target-limit projection equations. -/
theorem action_eq (a b : A)
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    (f : limit (K ⋙ EnrichedFunctorCat.evaluation a) ⊗ (a ⟶[V] b) ⟶
      limit (K ⋙ EnrichedFunctorCat.evaluation b))
    (hf : ∀ j, f ≫ limit.π (K ⋙ EnrichedFunctorCat.evaluation b) j =
      (limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)) :
    f = action K a b := by
  apply limit.hom_ext
  intro j
  exact (hf j).trans (action_projection K a b j).symm

end CategoryTheory.EnrichedFunctorCat.PointwiseLimit
