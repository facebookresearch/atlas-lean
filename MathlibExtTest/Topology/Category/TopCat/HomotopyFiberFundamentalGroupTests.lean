/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.TopCat.HomotopyFiberFundamentalGroup

/-!
# Clients of the complete homotopy-fiber group sequence

These clients use the actual ordinary source projection, the published Kan
characteristic equation, and the original connecting map's commutation and
injection properties for arbitrary pointed TopCat maps.
-/

noncomputable section

open CategoryTheory

universe u

namespace TopCat

/-- The actual ordinary source projection kills the canonical cube-based boundary. -/
theorem homotopyFiber_actual_projection_connecting_test {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) (a : HomotopyGroup.Pi 2 Y y) :
    FundamentalGroup.mapOfEq (homotopyFiberToTotal f y).hom
      (ConcreteCategory.congr_hom (homotopyFiberSelectedPointMap_toTotal f x y hxy) PUnit.unit)
      (homotopyFiberConnectingHom f x y hxy a) = 1 := by
  rw [← homotopyFiberFundamentalGroupProjection_eq_mapOfEq f x y hxy]
  exact homotopyFiberFundamentalGroupProjection_connecting f x y hxy a

/-- The original connecting map is read by the existing Kan connecting group homomorphism. -/
theorem homotopyFiber_connecting_native_test {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) (a : HomotopyGroup.Pi 2 Y y) :
    homotopyFiberFundamentalGroupMulEquiv f x y hxy (homotopyFiberConnectingHom f x y hxy a) =
      SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom
        (homotopyFiberFibrationSequence f x y hxy) 0
        (homotopyGroupSingularMulEquiv 1 Y y a) :=
  homotopyFiberConnectingHom_native f x y hxy a

/-- Every actual fiber loop commutes with the unchanged original boundary value. -/
theorem homotopyFiber_connecting_commute_test {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) (a : HomotopyGroup.Pi 2 Y y)
    (g : FundamentalGroup (homotopyFiber f y)
      (homotopyFiberSelectedPointMap f x y hxy PUnit.unit)) :
    Commute (homotopyFiberConnectingHom f x y hxy a) g := by
  rw [commute_iff_eq]
  exact (Subgroup.mem_center_iff.mp
    (homotopyFiberConnectingHom_range_le_center f x y hxy ⟨a, rfl⟩) g).symm

/-- The source pi-two criterion distinguishes the original second homotopy classes. -/
theorem homotopyFiber_connecting_eq_iff_test {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (hX : Subsingleton (HomotopyGroup.Pi 2 X x)) (a b : HomotopyGroup.Pi 2 Y y) :
    homotopyFiberConnectingHom f x y hxy a = homotopyFiberConnectingHom f x y hxy b ↔ a = b :=
  (homotopyFiberConnectingHom_injective f x y hxy hX).eq_iff

end TopCat

end
