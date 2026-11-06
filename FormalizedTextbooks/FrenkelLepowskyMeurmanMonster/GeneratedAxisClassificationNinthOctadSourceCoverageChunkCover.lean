/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacketCover

/-! Four consecutive sixty-four-address intervals cover an original source packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A sixty-four-address interval inside an original256-address source packet. -/
def generatedNinthCoverageChunkIndex (b : Fin 4) (m : Fin 64) : Fin 256 :=
  ⟨64 * b.val + m.val, by omega⟩

/-- Coverage of the four consecutive intervals implies coverage of the original source packet. -/
theorem generatedNinth_coverage_chunk_cover (P : Fin 256 → Prop)
    (h : ∀ b : Fin 4, ∀ m : Fin 64, P (generatedNinthCoverageChunkIndex b m)) :
    ∀ k : Fin 256, P k := by
  intro k
  let b : Fin 4 := ⟨k.val / 64, by omega⟩
  let m : Fin 64 := ⟨k.val % 64, by omega⟩
  have he : generatedNinthCoverageChunkIndex b m = k := by
    apply Fin.ext
    change 64 * b.val + m.val = k.val
    dsimp only [b, m]
    omega
  rw [← he]
  exact h b m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
