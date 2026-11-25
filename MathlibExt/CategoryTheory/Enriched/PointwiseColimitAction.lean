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
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Particular colimit actions for genuine enriched functors

Descend the full right Hom action through the original evaluated colimit
cocone. No ordinary category is required on the enriched index.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ

namespace CategoryTheory.EnrichedFunctorCat.PointwiseColimit
open Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)

/-- The original full Hom action followed by the target's selected colimit injection. -/
def actionCocone (a b : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)] :
    Cocone ((K ⋙ EnrichedFunctorCat.evaluation a) ⋙ tensorRight (a ⟶[V] b)) where
  pt := colimit (K ⋙ EnrichedFunctorCat.evaluation b)
  ι :=
    { app := fun j => MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) ≫
        colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j
      naturality := by
        intro i j f
        have hn := (K.map f).uncurriedNaturality a b
        have hc := colimit.w (K ⋙ EnrichedFunctorCat.evaluation b) f
        change (EnrichedFunctorCat.component (K.map f) a ▷ (a ⟶[V] b)) ≫
          (MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) ≫
            colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j) =
          (MonoidalClosed.uncurry ((K.obj i).toEnrichedFunctor.map a b) ≫
            colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) i) ≫ 𝟙 _
        let H := a ⟶[V] b
        let ai := MonoidalClosed.uncurry ((K.obj i).toEnrichedFunctor.map a b)
        let aj := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
        let ci : (K.obj i).toEnrichedFunctor.obj b ⟶
            colimit (K ⋙ EnrichedFunctorCat.evaluation b) :=
          colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) i
        let cj : (K.obj j).toEnrichedFunctor.obj b ⟶
            colimit (K ⋙ EnrichedFunctorCat.evaluation b) :=
          colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j
        let m := EnrichedFunctorCat.component (K.map f) b
        let t := EnrichedFunctorCat.component (K.map f) a
        have hNatural : ai ≫ m = (t ▷ H) ≫ aj := by
          simpa only [ai, aj, m, t, H, tensorHom_id] using hn
        have hCocone : m ≫ cj = ci := hc
        have hStart : (t ▷ H) ≫ (aj ≫ cj) = (ai ≫ m) ≫ cj :=
          (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ cj) hNatural.symm)
        have hEnd : (ai ≫ m) ≫ cj = ai ≫ ci :=
          (Category.assoc _ _ _).trans (congrArg (fun q => ai ≫ q) hCocone)
        change (t ▷ H) ≫ (aj ≫ cj) = (ai ≫ ci) ≫ 𝟙 _
        exact hStart.trans (hEnd.trans (Category.comp_id _).symm) }

/-- The full right Hom action on the actual pointwise colimit objects. -/
def action (a b : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)] :
    colimit (K ⋙ EnrichedFunctorCat.evaluation a) ⊗ (a ⟶[V] b) ⟶
      colimit (K ⋙ EnrichedFunctorCat.evaluation b) :=
  (isColimitOfPreserves (tensorRight (a ⟶[V] b))
    (colimit.isColimit (K ⋙ EnrichedFunctorCat.evaluation a))).desc (actionCocone K a b)

/-- Each original colimit injection intertwines the entire enriched Hom action. -/
theorem injection_action (a b : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)] (j : J) :
    (colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫
      action K a b =
    MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) ≫
      colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j :=
  (isColimitOfPreserves (tensorRight (a ⟶[V] b))
    (colimit.isColimit (K ⋙ EnrichedFunctorCat.evaluation a))).fac (actionCocone K a b) j

/-- The action is the unique descent with the specified full-Hom injection equations. -/
theorem action_eq (a b : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    (f : colimit (K ⋙ EnrichedFunctorCat.evaluation a) ⊗ (a ⟶[V] b) ⟶
      colimit (K ⋙ EnrichedFunctorCat.evaluation b))
    (hf : ∀ j : J,
      (colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫ f =
        MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) ≫
          colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j) :
    f = action K a b := by
  apply (isColimitOfPreserves (tensorRight (a ⟶[V] b))
    (colimit.isColimit (K ⋙ EnrichedFunctorCat.evaluation a))).hom_ext
  intro j
  exact (hf j).trans (injection_action K a b j).symm

end CategoryTheory.EnrichedFunctorCat.PointwiseColimit
