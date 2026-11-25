/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: @toskua
-/

module

public import MathlibExt.CategoryTheory.MorphismProperty.InverseTower
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Limits of inverse source-mapping towers

A fixed contravariant functor preserving limits sends every continuous source
diagram to a continuous inverse mapping tower. The predecessor cone and its
limiting witness retain the actual source objects and restriction maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w uC vC uV vV

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.OriginalInverseTowerLifting

variable {C : Type uC} [Category.{vC} C] {V : Type uV} [Category.{vV} V]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The actual principal mapping cone at the original stage m. -/
def precedingCone (D : Jᵒᵖ ⥤ C) (m : J) :
    Cone ((Set.principalSegIio m).monotone.functor.op ⋙ D) where
  pt := D.obj (op m)
  π := {
    app i := D.map (homOfLE i.unop.2.le).op
    naturality i j h := by
      dsimp
      rw [Category.id_comp, ← D.map_comp]
      rfl }

variable (G : Cᵒᵖ ⥤ V) [PreservesLimitsOfSize.{w, w} G]

/-- Fix the whole source functor before deriving the actual original principal mapping limit. -/
def sourcePrecedingIsLimit (Q : J ⥤ C) [Q.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) : IsLimit (precedingCone (Q.op ⋙ G) m) := by
  let c := (Set.principalSegIio m).cocone Q
  let hc := Q.isColimitOfIsWellOrderContinuous m hm
  change IsLimit (G.mapCone c.op)
  exact isLimitOfPreserves G hc.op

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
/-- The same predecessor limiting witnesses give continuity of the opposite mapping tower. -/
theorem sourceMappingWellOrderContinuous (Q : J ⥤ C) [Q.IsWellOrderContinuous] :
    (Q.op ⋙ G).rightOp.IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    let D := Q.op ⋙ G
    let R := (Set.principalSegIio m).monotone.functor.op ⋙ D
    have hLimit := sourcePrecedingIsLimit G Q m hm
    change IsLimit (coneOfCoconeRightOp (F := R)
      ((Set.principalSegIio m).cocone D.rightOp)) at hLimit
    exact ⟨isColimitOfConeOfCoconeRightOp R hLimit⟩

end CategoryTheory.OriginalInverseTowerLifting
