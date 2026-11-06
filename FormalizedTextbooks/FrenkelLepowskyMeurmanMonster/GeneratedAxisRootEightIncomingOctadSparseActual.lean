/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingOctadSparsePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingOctadSparsePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingOctadSparsePacket02

/-! Exhaustive sparse coefficient binding over the original 759 by 64 domain. -/
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem sparse_by_block (b : Fin 3) (o : Fin 759) (f : Fin 64)
    (hb : o.val / 253 = b.val) :
    generatedRootEightSparseCoefficient (generatedRootEightIncomingOctadSparseEntries o) f =
      generatedRootEightIncomingOctadPackedCoefficient o f := by
  fin_cases b
  · change o.val / 253 = 0 at hb
    let u : Fin 253 := ⟨o.val % 253, Nat.mod_lt _ (by decide)⟩
    have ho : (⟨0 + u.val, by omega⟩ : Fin 759) = o := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [ho] using generatedRootEight_incoming_octad_sparse_packet_00 u f
  · change o.val / 253 = 1 at hb
    let u : Fin 253 := ⟨o.val % 253, Nat.mod_lt _ (by decide)⟩
    have ho : (⟨253 + u.val, by omega⟩ : Fin 759) = o := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [ho] using generatedRootEight_incoming_octad_sparse_packet_01 u f
  · change o.val / 253 = 2 at hb
    let u : Fin 253 := ⟨o.val % 253, Nat.mod_lt _ (by decide)⟩
    have ho : (⟨506 + u.val, by omega⟩ : Fin 759) = o := by
      apply Fin.ext
      dsimp only [u]
      omega
    simpa only [ho] using generatedRootEight_incoming_octad_sparse_packet_02 u f


/-- Sparse lookup retains all original signed source slots, including every zero. -/
theorem generatedRootEight_incoming_octad_sparse_actual (o : Fin 759) (f : Fin 64) :
    generatedRootEightSparseCoefficient (generatedRootEightIncomingOctadSparseEntries o) f =
      generatedRootEightIncomingOctadPackedCoefficient o f :=
  sparse_by_block ⟨o.val / 253, by omega⟩ o f rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
