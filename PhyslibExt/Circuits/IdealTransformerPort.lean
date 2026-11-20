/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Ideal transformer port power

## i. Overview

An ideal two-port transformer with real turns ratio `n ≠ 0`, primary
pair `(V1, I1)` and secondary pair `(V2, I2)`, both currents
entering: `V1 = n * V2` and `I2 = -(n * I1)`. The net instantaneous
port power `V1 * I1 + V2 * I2` is then zero. The component adapter
packages the sign mapping: from the secondary voltage `V2` and the
entering primary current `I1` it produces the pair
`(n * V2, -(n * I1))`. No saturation, hysteresis, magnetizing
current, core loss or dynamics is modeled.

## ii. Key results

- `netPortPower_eq_zero_of_idealTransformer`: the headline power
  balance under the two port relations.
- `netPortPower_adapter_eq_zero`: the adapter output conserves
  power against its own inputs.
- `netPortPower_eq_zero_polarity_reversed_secondary`: negating both
  secondary variables preserves the balance.
- `netPortPower_flipped_secondary_current` and
  `netPortPower_flipped_secondary_current_ne_zero`: keeping `I2`
  an entering current but with the erroneous sign relation
  `I2 = n * I1` (the relation a leaving current would satisfy),
  the entering-power sum is `2 * (n * V2 * I1)`, nonzero whenever
  `n * V2 * I1 ≠ 0`: conservation depends on the entering-current
  sign.

## iii. Table of contents

- A. The ideal-transformer port model

## iv. References

- J. W. Nilsson and S. A. Riedel, *Electric Circuits*, eleventh
  edition, Pearson, 2019: the ideal-transformer terminal equations
  and the entering-current (passive sign) convention for port power.

## A. The ideal-transformer port model
-/

@[expose] public section

namespace PhyslibExt.Circuits.IdealTransformerPort

/-- Net instantaneous port power `V1 * I1 + V2 * I2` for primary pair
`(V1, I1)` and secondary pair `(V2, I2)`, both currents entering their
labeled ports. -/
def netPortPower (V1 I1 V2 I2 : ℝ) : ℝ :=
  V1 * I1 + V2 * I2

/-- The ideal-transformer component adapter: from the secondary
voltage `V2` and the entering primary current `I1`, the ordered pair
`(V1, I2) = (n * V2, -(n * I1))` of primary voltage and entering
secondary current. -/
def idealTransformerPort (n V2 I1 : ℝ) : ℝ × ℝ :=
  (n * V2, -(n * I1))

/-- The adapter's primary voltage is `n * V2`. -/
lemma idealTransformerPort_fst (n V2 I1 : ℝ) :
    (idealTransformerPort n V2 I1).1 = n * V2 := by
  rfl

/-- The adapter's secondary current is `-(n * I1)`: the entering-current
sign convention of the leaf. -/
lemma idealTransformerPort_snd (n V2 I1 : ℝ) :
    (idealTransformerPort n V2 I1).2 = -(n * I1) := by
  rfl

/-- At zero secondary voltage and zero primary current, the adapter
returns the zero port pair. -/
lemma idealTransformerPort_zero (n : ℝ) :
    idealTransformerPort n 0 0 = (0, 0) := by
  simp [idealTransformerPort]

/-- Headline result: for an ideal transformer with nonzero real turns
ratio `n`, voltage relation `V1 = n * V2`, and entering secondary
current `I2 = -(n * I1)`, the net instantaneous port power is zero. -/
lemma netPortPower_eq_zero_of_idealTransformer
    {n V1 V2 I1 I2 : ℝ} (hn : n ≠ 0)
    (hV : V1 = n * V2) (hI : I2 = -(n * I1)) :
    netPortPower V1 I1 V2 I2 = 0 := by
  unfold netPortPower
  rw [hV, hI]
  ring

/-- The adapter packages the headline: the port pair it returns from
`V2` and `I1` has zero net instantaneous power against the entering
currents `I1` (primary) and its own secondary current. -/
lemma netPortPower_adapter_eq_zero
    {n : ℝ} (hn : n ≠ 0) (V2 I1 : ℝ) :
    netPortPower (idealTransformerPort n V2 I1).1 I1
      V2 (idealTransformerPort n V2 I1).2 = 0 := by
  rw [idealTransformerPort_fst, idealTransformerPort_snd]
  exact netPortPower_eq_zero_of_idealTransformer hn rfl rfl

/-- The entering-current sign is essential: keep `I2` the entering
secondary current but give it the erroneous sign relation
`I2 = n * I1` (the relation a leaving secondary current would
satisfy), with `V1 = n * V2`. The entering-power sum
`netPortPower (n * V2) I1 V2 (n * I1)` is then `2 * (n * V2 * I1)`,
not zero in general: power conservation fails for the wrong
entering sign. This lemma does not reinterpret `I2` as a leaving
current; with a leaving current the entering-power formula itself
would be `V1 * I1 - V2 * I2`, a different function. -/
lemma netPortPower_flipped_secondary_current
    (n V2 I1 : ℝ) :
    netPortPower (n * V2) I1 V2 (n * I1) = 2 * (n * V2 * I1) := by
  unfold netPortPower
  ring

/-- Polarity reversal of both secondary variables: negating `V2` and
`I2` together, primary variables unchanged, preserves zero
net instantaneous port power. -/
lemma netPortPower_eq_zero_polarity_reversed_secondary
    {n V1 V2 I1 I2 : ℝ} (hn : n ≠ 0)
    (hV : V1 = n * V2) (hI : I2 = -(n * I1)) :
    netPortPower V1 I1 (-V2) (-I2) = 0 := by
  unfold netPortPower
  rw [hV, hI]
  ring

/-- In particular, with a nonzero turns ratio and nonzero `V2` and
`I1`, the erroneous entering sign gives nonzero net entering power,
so power conservation genuinely depends on the entering-current
sign. -/
lemma netPortPower_flipped_secondary_current_ne_zero
    {n V2 I1 : ℝ} (hn : n ≠ 0) (hV2 : V2 ≠ 0) (hI1 : I1 ≠ 0) :
    netPortPower (n * V2) I1 V2 (n * I1) ≠ 0 := by
  rw [netPortPower_flipped_secondary_current]
  exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hn hV2) hI1)

end PhyslibExt.Circuits.IdealTransformerPort
