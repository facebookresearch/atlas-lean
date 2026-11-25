/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergUniversal

/-!
# Original Steinberg universality in independent target universes

The existing original lift through each central extension works in arbitrary
kernel and total universes. Perfect-source uniqueness supplies the same
universal extension property in each of those universes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace AlgebraicKTheory

namespace StableSteinberg

/-- Original Steinberg lifts give universality in arbitrary kernel and total universes. -/
theorem steinbergExtension_isUniversalFor (R : Type u) [Ring R] :
    GroupExtension.IsUniversalFor.{u, u, u, v, w} (steinbergExtension R) := by
  refine ⟨steinbergExtension_isCentral R, ?_⟩
  intro N E _ _ S hS
  refine ⟨liftToCentralExtension S hS, rightHom_comp_liftToCentralExtension S hS, ?_⟩
  intro f hf
  exact MonoidHom.eq_of_comp_eq_of_ker_le_center hS
    (hf.trans (rightHom_comp_liftToCentralExtension S hS).symm)

end StableSteinberg

end AlgebraicKTheory

end
