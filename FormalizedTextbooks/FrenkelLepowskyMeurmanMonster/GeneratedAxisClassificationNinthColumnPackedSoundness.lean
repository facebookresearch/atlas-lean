/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedChunks

/-! Every packed coordinate agrees with the frozen original mask decoder.
The proof uses exact binary chunk identities, with no unchecked evaluation bridge. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generatedNinth_packed_chunk_bit (mask : ℕ) (n : Fin 4096) :
    ((mask >>> (64 * (n.val / 64))) &&& 0xffffffffffffffff).testBit (n.val % 64) =
      mask.testBit n.val := by
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  have hm : (0xffffffffffffffff : ℕ).testBit (n.val % 64) = true := by
    change (2 ^ 64 - 1 : ℕ).testBit (n.val % 64) = true
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Nat.mod_lt _ (by decide))
  rw [hm, Bool.and_true]
  congr 1
  omega

/-- All packed signs and magnitudes are exactly the original chronological integer data. -/
theorem generatedNinth_column_spin_packed (k : Fin 10) (n : Fin 4096) :
    generatedNinthColumnSpinPacked k n = generatedNinthColumnSpinData k n := by
  unfold generatedNinthColumnSpinPacked generatedNinthColumnSpinData
  dsimp only
  rw [← generatedNinth_column_packed_positive_chunks,
    ← generatedNinth_column_packed_magnitudeOne_chunks,
    ← generatedNinth_column_packed_magnitudeTwo_chunks,
    ← generatedNinth_column_packed_magnitudeFour_chunks]
  simp only [generatedNinth_packed_chunk_bit]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
