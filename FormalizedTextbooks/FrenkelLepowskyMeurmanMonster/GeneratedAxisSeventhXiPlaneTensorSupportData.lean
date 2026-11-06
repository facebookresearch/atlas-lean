/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorPackedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseData

/-! The actual tensor is supported on the two original triangle-sign kernels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The two genuine binary constraints on an original spin label. -/
def generatedSeventhXiTensorSupported (d : ℕ) : Prop :=
  monsterNortonBitParity (d &&& 1504) = false ∧
    monsterNortonBitParity (d &&& 1648) = false

instance (d : ℕ) : Decidable (generatedSeventhXiTensorSupported d) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All listed odd families are retained; this only proves where their codes lie.
/-- Every original odd family lies in both triangle-sign kernels. -/
theorem generatedSeventhXiTensorSupport_odd : ∀ g : Fin 232,
    generatedSeventhXiTensorSupported (generatedSeventhXiOddCodes g) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The checked original spin vector is tested at every one of its coordinates.
/-- The original canonical spin vector vanishes outside the two kernels. -/
theorem generatedSeventhXiTensorSupport_spin : ∀ d : Fin 4096,
    ¬ generatedSeventhXiTensorSupported d.val → generatedSeventhXiTensorSpin d = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- These finite identities account for the actual omega coordinate, rather than dropping it.
/-- Both low and omega-shifted labels have exactly the same two syndromes. -/
theorem generatedSeventhXiTensorSupport_low : ∀ d : Fin 4096,
    (generatedSeventhXiTensorSupported (generatedSeventhXiTensorLow d).val ↔
      generatedSeventhXiTensorSupported d.val) ∧
    (generatedSeventhXiTensorSupported ((generatedSeventhXiTensorLow d).val + 2048) ↔
      generatedSeventhXiTensorSupported d.val) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
