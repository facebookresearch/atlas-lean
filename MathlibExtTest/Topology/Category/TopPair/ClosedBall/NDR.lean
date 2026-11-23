/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.NDR

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u v

namespace MathlibExtTest.Topology.Category.TopPair.ClosedBall.NDR

variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

example : _root_.TopPair.NDRData
    (_root_.TopPair.closedBallPair.{u} (0 : E) 1) :=
  _root_.TopPair.closedUnitBallNDRData.{u} E

example (z : (_root_.TopPair.closedBallPair.{u} (0 : E) 1).fst) :
    (_root_.TopPair.closedUnitBallNDRData.{u} E).control z = 0 ↔
      ‖z.down.val‖ = 1 :=
  ((_root_.TopPair.closedUnitBallNDRData.{u} E).control_eq_zero_iff z).trans
    (_root_.TopPair.mem_range_closedUnitBallPair_map_iff z)

example : _root_.TopPair.closedUnitBallRadialScale (0 : E) = 2 := by
  simp [_root_.TopPair.closedUnitBallRadialScale]

example : _root_.TopCat.IsHurewiczCofibration
    (_root_.TopPair.closedBallPair.{u} (0 : E) 1).map :=
  _root_.TopPair.closedUnitBall_isHurewiczCofibration.{u} E

example : _root_.TopPair.NDRData
    (_root_.Topology.CWComplex.classicalCellDiskPair.{u} 0) :=
  _root_.Topology.CWComplex.classicalCellDiskPairNDRData.{u} 0

example (m : ℕ) : _root_.TopPair.GoodPairData
    (_root_.Topology.CWComplex.classicalCellDiskPair.{u} (m + 1)) :=
  _root_.Topology.CWComplex.classicalCellDiskPairGoodPairData.{u} m

example (n : ℕ) : _root_.TopCat.IsHurewiczCofibration
    (_root_.Topology.CWComplex.classicalCellDiskPair.{u} n).map :=
  _root_.Topology.CWComplex.classicalCellDiskPair_isHurewiczCofibration.{u} n

end MathlibExtTest.Topology.Category.TopPair.ClosedBall.NDR

end
