/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Cone
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.NerveCone
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.OrdinaryCone
import MathlibExt.AlgebraicTopology.Quasicategory.NerveTerminalVertex
import MathlibExt.AlgebraicTopology.Quasicategory.TerminalVertexIso

/-!
# Internal pullback conditions in ordinary nerves

The actual original coherent square gives its actual original cone
point. The all-degree native cone-category nerve isomorphism preserves
that point, so the native all-boundary condition is precisely ordinary
terminality of the original cone, with all four original maps retained.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe uObj uHom

namespace SSet.NativePullback

variable {C : Type uObj} [Category.{uHom} C]


/-- The generic native cone point is the same literal original square cone point. -/
theorem conePoint_eq_squareConePoint (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    sliceOver.conePoint (cospanInclusion ≫ nerveMapIndex Q) (coneDiagram (nerveMapIndex Q))
        (coneDiagram_fixed (nerveMapIndex Q)) =
      squareConePoint Q :=
  rfl

/-- All original boundary dimensions characterize terminality of the
given original ordinary cone, through genuine native comparisons. -/
theorem isPullbackSquare_nerve_iff_isTerminal (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    IsPullbackSquare (nerveMapIndex Q) ↔ Nonempty (IsTerminal (ordinaryCone Q)) := by
  refine (isPullbackSquare_iff_isTerminalVertex (nerveMapIndex Q)).trans ?_
  rw [conePoint_eq_squareConePoint]
  refine (isTerminalVertex_iff_of_iso (squareConePoint Q) (nerveConeIso Q)).trans ?_
  rw [squareConePoint_comp_nerveConeIso_hom]
  exact isTerminalVertex_nerve_iff (ordinaryCone Q)

/-- The complete native all-boundary condition in an ordinary nerve is
exactly the pullback of the four literal original maps. -/
theorem isPullbackSquare_nerve_iff_isPullback (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    IsPullbackSquare (nerveMapIndex Q) ↔
      IsPullback
        (Q.map (WithInitial.homTo (ULift.up WalkingCospan.left)))
        (Q.map (WithInitial.homTo (ULift.up WalkingCospan.right)))
        (Q.map (WithInitial.incl.map (show
          (ULift.up WalkingCospan.left : CospanObjects.{max uObj uHom}) ⟶
            ULift.up WalkingCospan.one from WalkingCospan.Hom.inl)))
        (Q.map (WithInitial.incl.map (show
          (ULift.up WalkingCospan.right : CospanObjects.{max uObj uHom}) ⟶
            ULift.up WalkingCospan.one from WalkingCospan.Hom.inr))) := by
  have ht : Nonempty (IsTerminal (ordinaryCone Q)) ↔ Nonempty (IsLimit (ordinaryCone Q)) :=
    ⟨fun ⟨h⟩ => ⟨(Limits.Cone.isLimitEquivIsTerminal (ordinaryCone Q)).symm h⟩,
      fun ⟨h⟩ => ⟨(Limits.Cone.isLimitEquivIsTerminal (ordinaryCone Q)) h⟩⟩
  exact (isPullbackSquare_nerve_iff_isTerminal Q).trans
    (ht.trans (ordinaryCone_isLimit_iff_isPullback Q))

end SSet.NativePullback
