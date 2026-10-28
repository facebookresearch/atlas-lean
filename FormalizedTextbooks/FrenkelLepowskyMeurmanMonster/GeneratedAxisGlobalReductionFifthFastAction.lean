/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthFastByteData

/-! Three exact byte lookups implement the genuine inverse-generator action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Three byte reads implement one inverse-generator action on the actual 24-bit domain. -/
def generatedAxisGlobalFifthFastInverse (k : Fin 19) (b : ℕ) : ℕ :=
  generatedAxisGlobalFifthInverseByteLookup k 0 (b % 256) ^^^
    generatedAxisGlobalFifthInverseByteLookup k 1 ((b / 256) % 256) ^^^
      generatedAxisGlobalFifthInverseByteLookup k 2 ((b / 65536) % 256)

/-- The cached computation is exactly the already proved actual inverse column action. -/
theorem generatedAxisGlobalFifthFastInverse_eq (k : Fin 19) (b : ℕ) (hb : b < 2 ^ 24) :
    generatedAxisGlobalFifthFastInverse k b =
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k) b := by
  have hh : b / 65536 < 256 := by omega
  have h0 := generatedAxisGlobalFifthInverseByte_certificate k 0
    ⟨b % 256, Nat.mod_lt _ (by decide)⟩
  have h1 := generatedAxisGlobalFifthInverseByte_certificate k 1
    ⟨(b / 256) % 256, Nat.mod_lt _ (by decide)⟩
  have h2 := generatedAxisGlobalFifthInverseByte_certificate k 2 ⟨b / 65536, hh⟩
  change generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k)
    ((b % 256) <<< 0) = generatedAxisGlobalFifthInverseByteLookup k 0 (b % 256) at h0
  change generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k)
    (((b / 256) % 256) <<< 8) =
      generatedAxisGlobalFifthInverseByteLookup k 1 ((b / 256) % 256) at h1
  change generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k)
    ((b / 65536) <<< 16) = generatedAxisGlobalFifthInverseByteLookup k 2 (b / 65536) at h2
  rw [Nat.shiftLeft_zero] at h0
  rw [generatedAxisGlobalFifthFastInverse, Nat.mod_eq_of_lt hh,
    ← h0, ← h1, ← h2, ← generatedAxisGlobalMaskRowsAction_three_bytes]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
