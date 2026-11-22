/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHPointedRealization
import MathlibExt.CategoryTheory.Adjunction.UnderPointRecords

/-!
# Full original pointed realization and singular adjunction records

The original direct adjunction and the same realization-of-zero-simplex
isomorphism give the whole original pointed adjunction. Its complete
functors are matched before the original unit, counit and both mate
directions are read back to their original underlying geometry.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory
open scoped Simplicial

namespace SSet.CGWHPointedAdjunctionRecords

open CategoryTheory.Adjunction.UnderPointRecords

/-- The entire original pointed realization retains the same direct functor and selected point inverse. -/
theorem left_record :
    SSet.pointedToCGWH.{u, v} = left (F := SSet.toCGWH.{u, v})
      (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}) := rfl

/-- The entire original pointed singular functor retains the same direct functor and original point unit. -/
theorem right_record :
    CGWH.pointedToSSet.{u, v} = right SSet.sSetCGWHAdj.{u, v}
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v} := rfl

/-- The entire original pointed adjunction keeps all original unit, counit and triangle records. -/
theorem adjunction_record :
    SSet.pointedToCGWHAdjunction.{u, v} = adjunction SSet.sSetCGWHAdj.{u, v}
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v} := rfl

/-- The complete original realization record retains its same underlying direct realization before projection. -/
theorem left_forget_record :
    SSet.pointedToCGWH.{u, v} ⋙ Under.forget CGWH.point =
      Under.forget (Δ[0] : SSet.{v}) ⋙ SSet.toCGWH.{u, v} := by
  rw [left_record]
  exact left_forget _

/-- The complete original singular record retains its underlying direct singular functor before projection. -/
theorem right_forget_record :
    CGWH.pointedToSSet.{u, v} ⋙ Under.forget (Δ[0] : SSet.{v}) =
      Under.forget CGWH.point.{u, v} ⋙ (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}) := by
  rw [right_record]
  exact right_forget _ _

/-- The same actual original pointed unit retains the whole direct realization-unit map. -/
theorem unit_right (X : Under (Δ[0] : SSet.{v})) :
    (SSet.pointedToCGWHAdjunction.{u, v}.unit.app X).right = SSet.sSetCGWHAdj.{u, v}.unit.app X.right := by
  rw [adjunction_record]
  exact CategoryTheory.Adjunction.UnderPointRecords.unit_right _ _ X

/-- The same actual original pointed counit retains the whole direct realization-counit map. -/
theorem counit_right (Y : Under CGWH.point.{u, v}) :
    (SSet.pointedToCGWHAdjunction.{u, v}.counit.app Y).right = SSet.sSetCGWHAdj.{u, v}.counit.app Y.right := by
  rw [adjunction_record]
  exact CategoryTheory.Adjunction.UnderPointRecords.counit_right _ _ Y

/-- The original pointed mate retains the same complete direct unit and underlying map. -/
theorem homEquiv_right (X : Under (Δ[0] : SSet.{v})) (Y : Under CGWH.point.{u, v})
    (p : SSet.pointedToCGWH.obj X ⟶ Y) :
    (SSet.pointedToCGWHAdjunction.homEquiv X Y p).right = SSet.sSetCGWHAdj.homEquiv X.right Y.right p.right := by
  rw [adjunction_record]
  exact CategoryTheory.Adjunction.UnderPointRecords.homEquiv_right _ _ X Y p

/-- The same selected original inverse pointed mate retains the complete direct counit and underlying map. -/
theorem homEquiv_symm_right (X : Under (Δ[0] : SSet.{v})) (Y : Under CGWH.point.{u, v})
    (p : X ⟶ CGWH.pointedToSSet.obj Y) :
    ((SSet.pointedToCGWHAdjunction.homEquiv X Y).symm p).right =
      (SSet.sSetCGWHAdj.homEquiv X.right Y.right).symm p.right := by
  rw [adjunction_record]
  exact CategoryTheory.Adjunction.UnderPointRecords.homEquiv_symm_right _ _ X Y p

end SSet.CGWHPointedAdjunctionRecords
