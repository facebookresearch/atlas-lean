/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddFastByteData

/-! Three exact byte lookups implement the genuine inverse-generator action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Three byte reads implement one inverse-generator action on the actual 24-bit domain. -/
def generatedAxisGlobalOddFastInverse (k : Fin 14) (b : ℕ) : ℕ :=
  generatedAxisGlobalOddInverseByteLookup k 0 (b % 256) ^^^
    generatedAxisGlobalOddInverseByteLookup k 1 ((b / 256) % 256) ^^^
      generatedAxisGlobalOddInverseByteLookup k 2 ((b / 65536) % 256)

/-- The cached computation is exactly the already proved actual inverse column action. -/
theorem generatedAxisGlobalOddFastInverse_eq (k : Fin 14) (b : ℕ) (hb : b < 2 ^ 24) :
    generatedAxisGlobalOddFastInverse k b =
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddInverseRows k) b := by
  have hh : b / 65536 < 256 := by omega
  have h0 := generatedAxisGlobalOddInverseByte_certificate k 0
    ⟨b % 256, Nat.mod_lt _ (by decide)⟩
  have h1 := generatedAxisGlobalOddInverseByte_certificate k 1
    ⟨(b / 256) % 256, Nat.mod_lt _ (by decide)⟩
  have h2 := generatedAxisGlobalOddInverseByte_certificate k 2 ⟨b / 65536, hh⟩
  change generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddInverseRows k)
    ((b % 256) <<< 0) = generatedAxisGlobalOddInverseByteLookup k 0 (b % 256) at h0
  change generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddInverseRows k)
    (((b / 256) % 256) <<< 8) =
      generatedAxisGlobalOddInverseByteLookup k 1 ((b / 256) % 256) at h1
  change generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddInverseRows k)
    ((b / 65536) <<< 16) = generatedAxisGlobalOddInverseByteLookup k 2 (b / 65536) at h2
  rw [Nat.shiftLeft_zero] at h0
  rw [generatedAxisGlobalOddFastInverse, Nat.mod_eq_of_lt hh,
    ← h0, ← h1, ← h2, ← generatedAxisGlobalMaskRowsAction_three_bytes]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
