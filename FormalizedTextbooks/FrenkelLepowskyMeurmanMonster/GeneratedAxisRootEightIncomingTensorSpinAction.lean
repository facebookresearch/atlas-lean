/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorAddress
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorStart
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorPair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorPair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorPair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorPair03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitNormalization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinLabelXor

/-! All original incoming spin coefficients follow from the four complete integer circuits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire genuine compact action on the full original source has its exact integer replay. -/
theorem generatedRootEight_incoming_tensor_spin_integer_action (r : Fin 8) :
    (generatedRootEightIncomingCompactSpin 0).val
      ((16 : ℝ) • nortonUIntegerEmbed (generatedRootEightIncomingTensorSourceCache r)) =
        nortonUIntegerEmbed (generatedRootEightIncomingTensorSpinInteger r) := by
  exact generatedRootEight_incoming_tensor_circuit_replay r
    generatedRootEight_incoming_tensor_addresses
    (fun k n => generatedTwelfth_spin_label_xor k n)
    (generatedRootEight_incoming_tensor_start r)
    (generatedRootEight_incoming_tensor_pair_00 r)
    (generatedRootEight_incoming_tensor_pair_01 r)
    (generatedRootEight_incoming_tensor_pair_02 r)
    (generatedRootEight_incoming_tensor_pair_03 r)

/-- Every actual incoming real spin coordinate has the exact full square-root denominator. -/
theorem generatedRootEight_incoming_tensor_spin_actual (r : Fin 8) (t : SpinIndex) :
    generatedRootEightIncomingTensorSpin r t =
      (generatedRootEightIncomingTensorSpinInteger r (nortonUIntegerLabel t) : ℝ) /
        (16 * Real.sqrt 2) := by
  exact generatedRootEight_incoming_tensor_spin_normalization r
    (generatedRootEight_incoming_tensor_spin_integer_action r) t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
