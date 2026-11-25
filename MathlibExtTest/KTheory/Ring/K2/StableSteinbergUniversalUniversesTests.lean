/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergUniversalUniverses
public import MathlibExt.GroupTheory.GroupExtension.UniversalFunctoriality

/-!
# Original Steinberg lift clients with independent target universes
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace AlgebraicKTheory.StableSteinberg

/-- Universality retains the original projection and arbitrary original target groups. -/
theorem universal_original_projection_test (R : Type u) [Ring R]
    {N : Type v} {E : Type w} [Group N] [Group E]
    (S : GroupExtension N E (StableE R)) (hS : S.IsCentral) :
    ∃! f : StableSteinberg R →* E, S.rightHom.comp f = toStableE :=
  (steinbergExtension_isUniversalFor R).2 S hS

/-- The canonical universal lift is the existing original Steinberg lift. -/
theorem universal_original_lift_test (R : Type u) [Ring R]
    {N : Type v} {E : Type w} [Group N] [Group E]
    (S : GroupExtension N E (StableE R)) (hS : S.IsCentral) :
    GroupExtension.IsUniversalFor.lift (steinbergExtension_isUniversalFor R) S hS
        (MonoidHom.id (StableE R)) = liftToCentralExtension S hS := by
  symm
  apply GroupExtension.IsUniversalFor.lift_unique
  rw [MonoidHom.id_comp]
  exact rightHom_comp_liftToCentralExtension S hS

end AlgebraicKTheory.StableSteinberg

end
