/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory

/-!
# Cofibrancy in the named Joyal model

Every object is cofibrant because the actual Joyal cofibrations are
monomorphisms. This common module supplies the original Joyal--Tierney
and coherent Joyal--Bergner comparisons.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace JoyalSSet

/-- Every object is cofibrant in the actual Joyal model, using its Mono classifier. -/
theorem isCofibrant (A : JoyalSSet.{u}) :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    IsCofibrant A := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  rw [isCofibrant_iff_of_isInitial (initial.to A) initialIsInitial,
    HomotopicalAlgebra.cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations (initial.to A)
  rw [JoyalSSet.modelCategory_cofibrations]
  have hI : IsInitial (JoyalSSet.forget.obj (⊥_ JoyalSSet.{u})) :=
    (initialIsInitial : IsInitial (⊥_ JoyalSSet.{u})).isInitialObj JoyalSSet.forget _
  let _ : Mono (JoyalSSet.forget.map (initial.to A)) := hI.mono_from _
  exact JoyalSSet.forget.mono_of_mono_map inferInstance

end JoyalSSet
