/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyModel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Cofibrancy of every designated simplicial space

The named Reedy model has monomorphism cofibrations. The original initial
arrow is monic because both evaluations carry its source to an initial type.
No global model or initial-monomorphism class is installed.
-/

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SimplicialSpace.ReedyModel

private theorem mono_initial_to (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    Mono (initial.to X) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  apply (SimplicialSpace.mono_forget_map_iff (initial.to X)).mp
  apply (NatTrans.mono_iff_mono_app (SimplicialSpace.forget.map (initial.to X))).2
  intro m
  apply (NatTrans.mono_iff_mono_app
    ((SimplicialSpace.forget.map (initial.to X)).app m)).2
  intro n
  have hRaw : IsInitial (SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u})) :=
    initialIsInitial.isInitialObj SimplicialSpace.forget (⊥_ SimplicialSpace.{u})
  have hOuter : IsInitial ((SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u})).obj m) :=
    hRaw.isInitialObj ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m)
      (SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u}))
  have hType : IsInitial (((SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u})).obj m).obj n) :=
    hOuter.isInitialObj ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)
      ((SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u})).obj m)
  let _ : IsEmpty (((SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u})).obj m).obj n) :=
    (Types.initial_iff_empty _).mp ⟨hType⟩
  exact (mono_iff_injective _).2 (Function.injective_of_subsingleton _)

/-- Every designated simplicial space is cofibrant in the same named Reedy model. -/
theorem isCofibrant (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HomotopicalAlgebra.IsCofibrant X := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.isCofibrant_iff]
  exact (cofibration_iff (initial.to X)).2 (mono_initial_to X)

end SimplicialSpace.ReedyModel
