/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.GroupTheory.GroupExtension.SecondHomologySplitting

/-!
# Original projection and independent-universe clients of second-homology recognition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w x y

namespace GroupExtension

/-- Native second homology yields the unique section of the unchanged original projection. -/
theorem secondHomology_original_projection_section_test
    {N : Type v} {E : Type w} {G : Type u} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G) (hS : S.IsCentral) [Group.IsPerfect G]
    (h₂ : IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) 2)) :
    ∃! σ : G →* E, S.rightHom.comp σ = MonoidHom.id G := by
  obtain ⟨σ⟩ := IsCentral.nonempty_splitting_of_isZero_secondHomology S hS h₂
  have hσ : S.rightHom.comp σ.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext σ.rightHom_splitting
  refine ⟨σ.toMonoidHom, hσ, fun f hf => ?_⟩
  exact MonoidHom.eq_of_comp_eq_of_ker_le_center hS (hf.trans hσ.symm)

/-- The original universality square permits independent target kernel and total universes. -/
theorem secondHomology_original_universe_lift_test
    {N : Type v} {E : Type w} {G : Type u} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G) (hS : S.IsCentral) [Group.IsPerfect E]
    (h₂ : IsZero (groupHomology (Rep.trivial (ULift.{w} ℤ) E (ULift.{w} ℤ)) 2))
    {K : Type x} {D : Type y} [Group K] [Group D]
    (T : GroupExtension K D G) (hT : T.IsCentral) :
    ∃! f : E →* D, T.rightHom.comp f = S.rightHom :=
  (hS.isUniversalFor_of_isZero_secondHomology h₂).2 T hT

end GroupExtension

end
