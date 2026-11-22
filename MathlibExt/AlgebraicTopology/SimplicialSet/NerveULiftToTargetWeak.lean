/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTarget

/-!
# The same original nerve weakness at shared universes

The actual contained target lift is an isomorphism. The full original
coefficient universe lift preserves and reflects every weak map, so the
existing original nerve adapter has precisely the same weak property
as the same original nerve map when both category universes coincide.
-/

noncomputable section

universe u v

open CategoryTheory

namespace SSet

variable {A B : Type u} [Category.{v} A] [Category.{v} B]

/-- The full original nerve adapter retains exactly the same original weak-map property at coinciding category
universes. -/
theorem nerveMapULiftToTarget_weak_iff (F : A ⥤ B) :
    realizationWeakEquivalences (nerveMapULiftToTarget.{u,0,v,0} F) ↔
      realizationWeakEquivalences (nerveMap F) := by
  let p := uliftFunctor.{max u v,max u v}.map (nerveMap F)
  let e := uliftContainedIso.{max u v,0} (nerve B)
  have h : nerveMapULiftToTarget.{u,0,v,0} F = p ≫ e.hom := rfl
  rw [h]
  exact (realizationWeakEquivalences.cancel_right_of_respectsIso p e.hom).trans
    (realizationWeak_ulift_map_iff (nerveMap F))

end SSet
