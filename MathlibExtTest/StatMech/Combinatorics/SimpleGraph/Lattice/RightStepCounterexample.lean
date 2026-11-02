/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RightStepCounterexample
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.RightStepCounterexample`

* The counterexample walk `edc_Vc` (the ring around the origin and back): the origin is isolated
  off it (`edc_isolated_reachable_eq`) and outside it (`edc_z_outside`), and the right-step and
  dodge properties fail (`edc_rightStep_refuted`, `edc_rightDodge_refuted`).
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RightStepCounterexample

example {w : Site 2} (h : (offSupport edc_Vc).Reachable (![(0 : ℤ), 0] : Site 2) w) :
    w = ![0, 0] := edc_isolated_reachable_eq h

example : (![(0 : ℤ), 0] : Site 2) ∉ jec_leftRegion edc_Vc := edc_z_outside

example : ¬ ecc_RightStep edc_Vc 2 := edc_rightStep_refuted 2

example : ¬ ecc_RightDodge edc_Vc 0 := edc_rightDodge_refuted 0

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RightStepCounterexample
