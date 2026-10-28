/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedSoundness

/-! The first original signed permutation transition uses the proved packed decoder. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check all original signed permutation coordinates through the proved integer decoder.
/-- Every first-transition coordinate follows the original P1 operator, including its phase. -/
theorem generatedNinth_column_packed_permutation_one : ∀ n : Fin 4096,
    generatedSixthIntegerPermutationFast 1 (generatedNinthColumnSpinPacked 0) n =
      generatedNinthColumnSpinPacked 1 n := by
  decide +kernel

/-- The whole first cache transition is the genuine original spin permutation. -/
theorem generatedNinth_column_packed_permutation_one_actual :
    generatedNinthIntegerPermutation 1 (generatedNinthColumnSpinData 0) =
      generatedNinthColumnSpinData 1 := by
  calc
    _ = generatedSixthIntegerPermutationFast 1 (generatedNinthColumnSpinPacked 0) := by
      rw [generatedNinth_column_permutation_fast]
      congr 1
      funext n
      exact (generatedNinth_column_spin_packed 0 n).symm
    _ = generatedNinthColumnSpinPacked 1 := by
      funext n
      exact generatedNinth_column_packed_permutation_one n
    _ = generatedNinthColumnSpinData 1 := by
      funext n
      exact generatedNinth_column_spin_packed 1 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
