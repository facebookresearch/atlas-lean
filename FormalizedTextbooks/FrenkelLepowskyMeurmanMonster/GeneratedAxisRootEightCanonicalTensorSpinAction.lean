/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorAddress
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorStart
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorPair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorPair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorPair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorPair03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveTensorColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalTensorInteger

/-! The complete positive canonical tensor follows from the full original final-axis columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every genuine canonical spin column acts on the entire original final tensor numerator. -/
theorem generatedRootEight_canonical_tensor_spin_integer_action (j : Fin 24) :
    (generatedRootEightCompactSpin 12).val
      ((16 : ℝ) • nortonUIntegerEmbed
        (fun n => generatedRootEightPositiveFinalTensorNumerator n j)) =
      nortonUIntegerEmbed (generatedRootEightCanonicalTensorSpinInteger j) := by
  exact generatedRootEight_canonical_tensor_circuit_vector_replay j _
    generatedRootEight_canonical_tensor_addresses
    (fun k n => generatedTwelfth_spin_label_xor k n)
    (generatedRootEight_canonical_tensor_start j)
    (generatedRootEight_canonical_tensor_pair_00 j)
    (generatedRootEight_canonical_tensor_pair_01 j)
    (generatedRootEight_canonical_tensor_pair_02 j)
    (generatedRootEight_canonical_tensor_pair_03 j)

/-- Every complete positive canonical tensor entry retains the full original square-root normalization. -/
theorem generatedRootEight_canonical_positive_tensor_integer (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
      (generatedRootEightCanonicalPositiveTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
        (8192 * Real.sqrt 2) := by
  have hs (j : Fin 24) (u : SpinIndex) :
      (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).2.2 u j =
        (generatedRootEightPositiveFinalTensorNumerator (nortonUIntegerLabel u) j : ℝ) /
          (128 * Real.sqrt 2) := by
    simpa only [nortonUIntegerLabel_inverse] using
      generatedRootEight_positive_final_tensor_integer (nortonUIntegerLabel u) j
  have h := generatedRootEight_canonical_positive_tensor_normalization
    generatedRootEightIncomingPositiveTrialityDestination
    (fun j n => generatedRootEightPositiveFinalTensorNumerator n j)
    (128 * Real.sqrt 2) hs generatedRootEight_canonical_tensor_spin_integer_action t i
  change (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i = _ at h
  simpa only [show (64 : ℝ) * (128 * Real.sqrt 2) = 8192 * Real.sqrt 2 by ring] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
