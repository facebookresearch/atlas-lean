/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionSheetGauge
import Code.FrontierA.Z2GaugeTypedFKCylinder















open Finset
open scoped symmDiff

namespace StatMech.FrontierA

noncomputable section



theorem multibondDisorderFreeEnergy_sheet_eq_lowerComplementSurface
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val)
    (J : CubicalPlaquette a b c -> Real) :
    multibondDisorderFreeEnergy
        (cubicalDualEnds (a := a) (b := b) (c := c)) J
        (cubicalXYSheet (a := a) (b := b) (c := c) k) =
      multibondDisorderFreeEnergy
        (cubicalDualEnds (a := a) (b := b) (c := c)) J
        (cubicalLowerComplementSurface (a := a) (b := b) (c := c) k) := by
  have hgauge := multibondDisorderFreeEnergy_symmDiff_cut
    (cubicalDualEnds (a := a) (b := b) (c := c)) J
    (cubicalXYSheet (a := a) (b := b) (c := c) k)
    (cubicalBelowSpin (a := a) (b := b) (c := c) k)
  rw [belowCut_eq_sheet_symmDiff_complement k hk,
    symmDiff_symmDiff_cancel_left] at hgauge
  exact hgauge.symm

end

end StatMech.FrontierA
