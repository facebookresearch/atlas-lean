/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6Packet15

/-! The step 6 original signed permutation transition uses the proved packed decoder. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generatedNinth_column_packed_permutation_6_blocks
    (k : Fin 16) (m : Fin 256) :
    generatedSixthIntegerPermutationFast 0 (generatedNinthColumnSpinPacked 5)
        ⟨256 * k.val + m.val, by omega⟩ =
      generatedNinthColumnSpinPacked 6 ⟨256 * k.val + m.val, by omega⟩ := by
  fin_cases k
  · exact generatedNinth_column_packed_permutation_6_packet_00 m
  · exact generatedNinth_column_packed_permutation_6_packet_01 m
  · exact generatedNinth_column_packed_permutation_6_packet_02 m
  · exact generatedNinth_column_packed_permutation_6_packet_03 m
  · exact generatedNinth_column_packed_permutation_6_packet_04 m
  · exact generatedNinth_column_packed_permutation_6_packet_05 m
  · exact generatedNinth_column_packed_permutation_6_packet_06 m
  · exact generatedNinth_column_packed_permutation_6_packet_07 m
  · exact generatedNinth_column_packed_permutation_6_packet_08 m
  · exact generatedNinth_column_packed_permutation_6_packet_09 m
  · exact generatedNinth_column_packed_permutation_6_packet_10 m
  · exact generatedNinth_column_packed_permutation_6_packet_11 m
  · exact generatedNinth_column_packed_permutation_6_packet_12 m
  · exact generatedNinth_column_packed_permutation_6_packet_13 m
  · exact generatedNinth_column_packed_permutation_6_packet_14 m
  · exact generatedNinth_column_packed_permutation_6_packet_15 m

/-- Every original coordinate follows the exact signed permutation operator. -/
theorem generatedNinth_column_packed_permutation_6 (n : Fin 4096) :
    generatedSixthIntegerPermutationFast 0 (generatedNinthColumnSpinPacked 5) n =
      generatedNinthColumnSpinPacked 6 n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using generatedNinth_column_packed_permutation_6_blocks k m

/-- The whole step 6 cache transition is the genuine original spin permutation. -/
theorem generatedNinth_column_packed_permutation_6_actual :
    generatedNinthIntegerPermutation 0 (generatedNinthColumnSpinData 5) =
      generatedNinthColumnSpinData 6 := by
  calc
    _ = generatedSixthIntegerPermutationFast 0 (generatedNinthColumnSpinPacked 5) := by
      rw [generatedNinth_column_permutation_fast]
      congr 1
      funext n
      exact (generatedNinth_column_spin_packed 5 n).symm
    _ = generatedNinthColumnSpinPacked 6 := by
      funext n
      exact generatedNinth_column_packed_permutation_6 n
    _ = generatedNinthColumnSpinData 6 := by
      funext n
      exact generatedNinth_column_spin_packed 6 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
