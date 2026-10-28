/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingSpatialCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingPositiveTensorNumeratorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSpinAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightIncomingShortCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightShortCache

/-! Every genuine positive incoming tensor entry has its complete integer numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every positive incoming tensor entry has the genuine denominator sixty-four root two. -/
theorem generatedRootEight_incoming_positive_tensor_integer (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).2.2 t i =
      (generatedRootEightIncomingPositiveTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
        (64 * Real.sqrt 2) := by
  rw [generatedRootEight_incoming_positive_tensor_coordinate]
  simp_rw [generatedRootEight_incoming_tensor_spin_actual]
  simp only [generatedRootEightIncomingPositiveTensorNumerator,
    Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The explicitly positive destination retains the full signed original short cache. -/
theorem generatedRootEight_incoming_positive_short_integer (r : GriessShortIndex) :
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).2.1 r =
      (generatedFifthRootEightShortCachedCoefficient r : ℝ) / 16 := by
  rw [generatedRootEight_incoming_positive_matrix_short.2,
    generatedFifthRootEight_incoming_short_actual,
    generatedFifthRootEight_short_cached_coefficient_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
