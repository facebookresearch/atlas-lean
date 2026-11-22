/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Reedy cofibrancy for simplex diagrams valued in CSS.
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialObject.CoefficientPreservation
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Reedy cofibrancy of simplicial diagrams of simplicial spaces

Every simplicial diagram valued in simplicial spaces has monomorphic latching maps, obtained by
evaluating both simplicial coefficient directions and using the Set-valued Eilenberg–Zilber
property. With the named Rezk model as coefficient model, every such diagram is cofibrant in the
associated Reedy model.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
open scoped Simplicial

namespace CSSValuedSimplexReedyAdapter

private theorem raw_initial_to_mono (Y : SimplicialObject SSet.{u}) :
    Mono (initial.to Y) := by
  apply (NatTrans.mono_iff_mono_app (initial.to Y)).2
  intro a
  apply (NatTrans.mono_iff_mono_app ((initial.to Y).app a)).2
  intro b
  let F : (SimplicialObject SSet.{u}) ⥤ Type u :=
    (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj a ⋙
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj b
  have h0 : IsInitial (F.obj (⊥_ (SimplicialObject SSet.{u}))) :=
    initialIsInitial.isInitialObj F _
  let _ : IsEmpty (((⊥_ (SimplicialObject SSet.{u})).obj a).obj b) :=
    (Types.initial_iff_empty _).mp ⟨h0⟩
  exact (mono_iff_injective _).mpr (Function.injective_of_subsingleton _)

/-- Absolute Set-valued latching monicity via the public EZ relative-class equality. -/
theorem raw_absolute_latching_mono (Y : SimplicialObject SSet.{u}) (n : ℕ) :
    Mono (SimplicialObject.latchingMap Y n) := by
  have hrel : SimplicialObject.reedyLeft (monomorphisms SSet.{u}) (initial.to Y) := by
    rw [SimplicialObject.reedyLeft_monomorphisms_eq]
    exact raw_initial_to_mono Y
  exact ((monomorphisms SSet.{u}).arrow_mk_iso_iff
    (SimplicialObject.relativeLatchingMapInitialArrowIso Y n)).mp (hrel n)

/-- The actual latching map of a CSS-valued simplex diagram is monic.
The two coefficient directions are evaluated; no latching/cofibrancy outcome is assumed. -/
theorem css_absolute_latching_mono
    (X : SimplicialObject SimplicialSpace.{u}) (n : ℕ) :
    Mono (SimplicialObject.latchingMap X n) := by
  apply (SimplicialSpace.mono_forget_map_iff
    (SimplicialObject.latchingMap X n)).mp
  apply (NatTrans.mono_iff_mono_app
    (SimplicialSpace.forget.map (SimplicialObject.latchingMap X n))).2
  intro a
  let F : SimplicialSpace.{u} ⥤ SSet.{u} :=
    SimplicialSpace.forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj a
  change Mono (F.map (SimplicialObject.latchingMap X n))
  let _ : Mono (SimplicialObject.latchingMap (X ⋙ F) n) :=
    raw_absolute_latching_mono (X ⋙ F) n
  rw [← (SimplicialObject.coefficientLatchingMap_equations F n X).1]
  infer_instance

/-- Cofibrancy is derived in the generic Reedy model over the literal named CSS model. -/
theorem css_simplex_all_objects_reedy_cofibrant
    (X : SimplicialObject SimplicialSpace.{u}) :
    let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
    let _ : HasInitial SimplicialSpace.{u} :=
      (SimplicialSpace.RezkModel.modelCategory.cm1b).out (Discrete PEmpty.{1})
    let _ : HasInitial (SimplicialObject SimplicialSpace.{u}) :=
      functorCategoryHasColimitsOfShape (J := Discrete PEmpty.{1})
        (K := SimplexCategoryᵒᵖ) (C := SimplicialSpace.{u})
    let _ : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
      SimplicialObject.reedyModelCategory
    IsCofibrant X := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
  let _ : HasInitial SimplicialSpace.{u} :=
    (SimplicialSpace.RezkModel.modelCategory.cm1b).out (Discrete PEmpty.{1})
  let _ : HasInitial (SimplicialObject SimplicialSpace.{u}) :=
    functorCategoryHasColimitsOfShape (J := Discrete PEmpty.{1})
      (K := SimplexCategoryᵒᵖ) (C := SimplicialSpace.{u})
  let _ : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
    SimplicialObject.reedyModelCategory
  apply (SimplicialObject.reedyModelCategory.isCofibrant_iff_latchingMapsIn X).mpr
  intro n
  change SimplicialSpace.RezkModel.modelCategory.categoryWithCofibrations.cofibrations
    (SimplicialObject.latchingMap X n)
  rw [SimplicialSpace.RezkModel.modelCategory_cofibrations]
  exact css_absolute_latching_mono X n

end CSSValuedSimplexReedyAdapter
