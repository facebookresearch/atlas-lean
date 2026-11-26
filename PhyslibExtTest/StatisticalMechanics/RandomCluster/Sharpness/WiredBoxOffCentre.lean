/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxOffCentre

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxOffCentre`

In `d = 2`, `q = 2`, `β = 1`:
* `transShellEvent_increasing`, `centeredShellEvent_increasing`;
* `wiredOuterInner_strictTranslationComparison` at the origin, box radius `5`, radius `k = 2`;
* `wiredOuterInnerDenom_le_eight_sig` at box radius `3`;
* `wired_outer_inner_differential_uniform_box` on the doubled box of radius `1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxOffCentre

open _root_.StatMech _root_.StatMech.OSSS
open Lattice IsingFK RevealmentConstruction TreeComplete
open RevealmentTranslation CenteredFirstHit
open FK WiredBoxLocalized WiredBoxOffCentre

-- The translated and centered shell events are increasing.
example : IsIncreasing (transShellEvent 2 1 (fun _ => 3)) ∧ IsIncreasing (centeredShellEvent 2 1) :=
  ⟨transShellEvent_increasing 2 1 _, centeredShellEvent_increasing 2 1⟩

-- Off-centre connection is bounded by the centered crossing (box radius `5`, `x = 0`, `k = 2`).
example : WiredBoxLocalized.wiredOuterInnerConn 2 5 2 1 0 2 ≤
    WiredBoxLocalized.wiredOuterInnerTheta 2 2 1 2 :=
  wiredOuterInner_strictTranslationComparison 2 5 2 1 (by norm_num) one_pos 0
    (by simp [Percolation.mem_boxFinset]) 2 (by simp) (by norm_num)

-- The OSSS denominator is bounded by eight times the profile sum.
example : WiredBoxLocalized.wiredOuterInnerDenom 2 3 2 1 ≤
    8 * WiredBoxLocalized.wiredOuterInnerSig 2 3 2 1 / ((3 : ℕ) : ℝ) :=
  wiredOuterInnerDenom_le_eight_sig 2 3 2 1 (by norm_num) one_pos

-- The sharp differential inequality on the doubled box of radius `1` in `d = 2`.
example := wired_outer_inner_differential_uniform_box 2 1 le_rfl 2 1 1 (by norm_num) one_pos le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxOffCentre
