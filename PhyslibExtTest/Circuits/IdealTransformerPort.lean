/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.IdealTransformerPort
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.IdealTransformerPort

namespace PhyslibExtTest.Circuits.IdealTransformerPort

/-- The `n = 2` validation case at concrete values: `V2 = 3`,
`I1 = 4` give `V1 = 6`, `I2 = -8`, and net power `6 * 4 + 3 * -8 = 0`
through the public lemma. -/
example : netPortPower 6 4 3 (-8) = 0 :=
  netPortPower_eq_zero_of_idealTransformer (n := 2) (V1 := 6) (V2 := 3)
    (I1 := 4) (I2 := -8) (by norm_num) (by norm_num) (by norm_num)

/-- The adapter at the same values. -/
example : idealTransformerPort 2 3 4 = (6, -8) :=
  Prod.ext (by rw [idealTransformerPort_fst]; norm_num)
    (by rw [idealTransformerPort_snd]; norm_num)

/-- Polarity reversal of both secondary variables at the same
values: `6 * 4 + (-3) * 8 = 0`. This is the case whose earlier
encoding with the primary voltage negated as well is false
(`-6 * 4 + (-3) * 8 = -48` in the wrong sign arrangement). -/
example : netPortPower 6 4 (-3) 8 = 0 := by
  have h := netPortPower_eq_zero_polarity_reversed_secondary (n := 2) (V1 := 6)
    (V2 := 3) (I1 := 4) (I2 := -8) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- The erroneous entering sign breaks conservation: with `I2`
still entering but satisfying `I2 = 2 * I1` in place of
`I2 = -(2 * I1)`, the net entering power is `2 * (2 * 3 * 4) = 48`,
through the public lemma and by direct computation. -/
example : netPortPower (2 * 3) 4 3 (2 * 4) = 48 := by
  rw [netPortPower_flipped_secondary_current]
  norm_num

example : netPortPower (2 * 3) 4 3 (2 * 4) ≠ 0 :=
  netPortPower_flipped_secondary_current_ne_zero (by norm_num) (by norm_num)
    (by norm_num)

end PhyslibExtTest.Circuits.IdealTransformerPort
