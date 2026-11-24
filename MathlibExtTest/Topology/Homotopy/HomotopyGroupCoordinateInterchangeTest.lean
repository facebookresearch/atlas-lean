/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import MathlibExt.Topology.Homotopy.HomotopyGroupCoordinateInterchange

set_option autoImplicit false
noncomputable section
universe u v
open scoped unitInterval Topology

namespace MathlibExtTest.HomotopyGroupCoordinateInterchange

/-- An infinite coordinate cube keeps the inverse transposition class after any target map. -/
theorem infiniteCoordinateSwap_map_inverse {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X}
    (f : C(X, Y)) (p : GenLoop ℤ X x) :
    HomotopyGroup.mk (GenLoop.map f (GenLoop.congr x (Equiv.swap (0 : ℤ) 1) p)) =
      (HomotopyGroup.mapHom f (HomotopyGroup.mk p))⁻¹ := by
  have h := HomotopyGroup.CoordinateInterchange.swap_class_eq_inverse
    (0 : ℤ) 1 (by omega) p
  calc
    _ = HomotopyGroup.mapHom f
        (HomotopyGroup.mk (GenLoop.congr x (Equiv.swap (0 : ℤ) 1) p)) := rfl
    _ = HomotopyGroup.mapHom f ((HomotopyGroup.mk p)⁻¹) :=
      congrArg (HomotopyGroup.mapHom f) h
    _ = _ := map_inv (HomotopyGroup.mapHom f) (HomotopyGroup.mk p)

end MathlibExtTest.HomotopyGroupCoordinateInterchange
