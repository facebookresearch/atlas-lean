/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortQBitAction

/-! Packed complete binary columns and quadratic phase rows for the actual corrected Xi. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All twenty-four genuine image columns, with both twelve-bit halves. -/
def generatedSeventhXiShortQColumnsBits : ℕ :=
  0x158886a3d7959277f537a8165d1008da20dbcf28dd360397 +
  (0x300b9600070a13670c001800466000ff2f4f0b007e1920ee <<< 192) +
  (0xc920d95300061d81ee0e027e050a78278b902183902f89e8 <<< 384)

/-- All twenty-four genuine phase rows, including the linear diagonal terms. -/
def generatedSeventhXiShortQPhaseRowsBits : ℕ :=
  0xb90680fd35009317c0ee26e02780d8c451c0c430f0b90406 +
  (0x390000004000802000801000800000fd34000000006e2100 <<< 192) +
  (0x800000800000000000200000280000b800003a00001f0000 <<< 384)

/-- Read a complete actual binary image column. -/
def generatedSeventhXiShortQColumnPacked (j : Fin 24) : ℕ :=
  (generatedSeventhXiShortQColumnsBits >>> (24 * j.val)) % 16777216

/-- Read a complete actual central phase row. -/
def generatedSeventhXiShortQPhaseRowPacked (i : Fin 24) : ℕ :=
  (generatedSeventhXiShortQPhaseRowsBits >>> (24 * i.val)) % 16777216

/-- Every packed column is exactly its original source value. -/
theorem generatedSeventhXiShortQColumnPacked_actual : ∀ j : Fin 24,
    generatedSeventhXiShortQColumnPacked j = generatedSeventhXiPlaneQColumns j := by
  decide +kernel

/-- Every packed row is exactly its original source value, retaining all central bits. -/
theorem generatedSeventhXiShortQPhaseRowPacked_actual : ∀ i : Fin 24,
    generatedSeventhXiShortQPhaseRowPacked i = generatedSeventhXiPlaneQPhaseRows i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
