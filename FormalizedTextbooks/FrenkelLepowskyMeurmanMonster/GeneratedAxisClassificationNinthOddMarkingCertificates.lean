/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkingPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkingPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkingPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkingPacket03

/-! Every original odd dictionary address is covered by a kernel coefficient packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The original final odd numerators identify all displayed markers and bound every other row. -/
theorem generatedNinth_odd_marking_integer_certificate (d : Fin 2048) (i : Fin 24) :
    (|generatedNinthFinalOddNumerator d i| = 8 ↔ (d, i) ∈ generatedNinthOddMarkings) ∧
      ((d, i) ∉ generatedNinthOddMarkings → |generatedNinthFinalOddNumerator d i| ≤ 2) := by
  have h : (|generatedNinthFinalOddNumerator d i| = 8 ↔
      (generatedNinthOddMarkingMask i).testBit d.val = true) ∧
      ((generatedNinthOddMarkingMask i).testBit d.val = false →
        |generatedNinthFinalOddNumerator d i| ≤ 2) := by
    if h0 : d.val < 512 then
      have heval : 0 + (d.val - 0) = d.val := by omega
      have he : (⟨0 + (d.val - 0), by omega⟩ : Fin 2048) = d := Fin.ext heval
      simpa only [he, heval] using generatedNinth_odd_marking_packet_00
        (⟨d.val - 0, by omega⟩ : Fin 512) i
    else if h1 : d.val < 1024 then
      have heval : 512 + (d.val - 512) = d.val := by omega
      have he : (⟨512 + (d.val - 512), by omega⟩ : Fin 2048) = d := Fin.ext heval
      simpa only [he, heval] using generatedNinth_odd_marking_packet_01
        (⟨d.val - 512, by omega⟩ : Fin 512) i
    else if h2 : d.val < 1536 then
      have heval : 1024 + (d.val - 1024) = d.val := by omega
      have he : (⟨1024 + (d.val - 1024), by omega⟩ : Fin 2048) = d := Fin.ext heval
      simpa only [he, heval] using generatedNinth_odd_marking_packet_02
        (⟨d.val - 1024, by omega⟩ : Fin 512) i
    else
      have heval : 1536 + (d.val - 1536) = d.val := by omega
      have he : (⟨1536 + (d.val - 1536), by omega⟩ : Fin 2048) = d := Fin.ext heval
      simpa only [he, heval] using generatedNinth_odd_marking_packet_03
        (⟨d.val - 1536, by omega⟩ : Fin 512) i
  constructor
  · exact h.1.trans (generatedNinth_odd_marking_mask_mem d i)
  · intro hn
    apply h.2
    cases hb : (generatedNinthOddMarkingMask i).testBit d.val
    · rfl
    · exact (hn ((generatedNinth_odd_marking_mask_mem d i).mp hb)).elim

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
