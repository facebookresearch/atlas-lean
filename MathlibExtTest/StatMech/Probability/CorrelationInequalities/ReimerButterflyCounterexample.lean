/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerButterflyCounterexample

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyCounterexample`

* `rbi_box_eq`: `rbi_A □ rbi_B = {FF, FT}`.
* `rbi_doubleCover_false`, `rbi_doubleCoverAll_false`: the butterfly double cover fails.
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyCounterexample

example : disjointOccurrence rbi_A rbi_B = {rbi_cfg false false, rbi_cfg false true} := rbi_box_eq

example : ¬ rdc_DoubleCover rbi_A rbi_B := rbi_doubleCover_false

example : ¬ rdc_DoubleCoverAll := rbi_doubleCoverAll_false

example : rbi_cfg true false ∉ rbi_B := by simp [rbi_B, rbi_cfg]

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyCounterexample
