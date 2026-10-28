/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddCoefficients

/-! Compact checked bit planes encode the exact sparse preferred middle odd-short numerators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The positive bit plane of the original preferred quarter numerators. -/
def generatedSixthMiddleOddPositiveMasks : Fin 24 → ℕ :=
  ![((0x880000000000 <<< 768) +
      (0x22 <<< 832) +
      (0x8000000000000 <<< 1920) +
      (0x20000000 <<< 1984)),
    ((0x4400000000 <<< 768) +
      (0x88000000 <<< 896) +
      (0x800000000000000 <<< 1536) +
      (0x800000000000 <<< 1728)),
    ((0x44 <<< 832) +
      (0x220000 <<< 896) +
      (0x40000 <<< 1280) +
      (0x400000000 <<< 1408)),
    ((0x110000000000 <<< 768) +
      (0x1100 <<< 832) +
      (0x440000 <<< 896) +
      (0x400000000 <<< 1024) +
      (0x4 <<< 1088) +
      (0x1000000 <<< 1152) +
      (0x1000000000000000 <<< 1216)),
    ((0x801 <<< 704) +
      (0x8000000000000 <<< 1216) +
      (0x400 <<< 1472)),
    ((0x10800000000 <<< 448) +
      (0x800000 <<< 1152) +
      (0x2000 <<< 1664)),
    ((0x4020000 <<< 192) +
      (0x2000 <<< 1088) +
      (0x4000000000000000 <<< 1344) +
      (0x20000000 <<< 1600) +
      (0x2000000000 <<< 1856)),
    ((0x20000000 <<< 1280) +
      (0x10000000000000 <<< 1536)),
    ((0x8400000000000000 <<< 576) +
      (0x2000000000000000 <<< 1216) +
      (0x1000000000000 <<< 1344)),
    ((0x8400000000000000 <<< 128) +
      (0x8400000000000000 <<< 256) +
      (0x84000000000000 <<< 576) +
      (0x800000000 <<< 1024) +
      (0x80000000000 <<< 1856)),
    ((0x2100000000000000 <<< 256) +
      (0x2000000 <<< 1152) +
      (0x80000 <<< 1600)),
    ((0x84000000000000 <<< 256) +
      (0x21000000000000 <<< 576)),
    ((0x28 <<< 384) +
      (0x200000000000 <<< 1728)),
    ((0x2800000000 <<< 64) +
      (0x14 <<< 384) +
      (0x280000 <<< 512) +
      (0x2000000000000 <<< 1920)),
    ((0x280000000000 <<< 64) +
      (0x100000000 <<< 1408) +
      (0x200000000000000 <<< 1536) +
      (0x80000000 <<< 1984)),
    ((0x1400000000 <<< 64) +
      (0x1400 <<< 384) +
      (0x4000000000000000 <<< 1216) +
      (0x1 <<< 1664) +
      (0x10000000000 <<< 1856)),
    ((0x4000000000000 <<< 960) +
      (0x400000 <<< 1280) +
      (0x4000000000 <<< 1408) +
      (0x8000000000000000 <<< 1536) +
      (0x80000000000 <<< 1728) +
      (0x80000000000000 <<< 1920) +
      (0x2000000 <<< 1984)),
    ((0x4000000000000 <<< 960) +
      (0x400000 <<< 1280) +
      (0x4000000000 <<< 1408) +
      (0x8000000000000000 <<< 1536) +
      (0x80000000000 <<< 1728) +
      (0x80000000000000 <<< 1920) +
      (0x2000000 <<< 1984)),
    ((0xbd2b000000000000 <<< 960)),
    ((0x42d0000000000000 <<< 960) +
      (0x4000000000 <<< 1024) +
      (0x40 <<< 1088) +
      (0x10000000 <<< 1152) +
      (0x100000000000000 <<< 1216) +
      (0x20000000000000 <<< 1344) +
      (0x2 <<< 1472) +
      (0x400000 <<< 1600) +
      (0x40 <<< 1664) +
      (0x10 <<< 1792) +
      (0x400000000000 <<< 1856)),
    (0x1001 +
      (0x800800000000 <<< 640) +
      (0x10000 <<< 1152) +
      (0x2000 <<< 1472) +
      (0x400000000 <<< 1856)),
    ((0x100100000000 <<< 640) +
      (0x40000000000 <<< 1408)),
    (0x2002 +
      (0x40040000 <<< 320) +
      (0x200200000000 <<< 640) +
      (0x200000 <<< 1984)),
    (0x8008 +
      (0x4000000 <<< 1280) +
      (0x8000000000 <<< 1728) +
      (0x800000000000000 <<< 1920))]

/-- The negative bit plane of the original preferred quarter numerators. -/
def generatedSixthMiddleOddNegativeMasks : Fin 24 → ℕ :=
  ![((0x11000000 <<< 896) +
      (0x1 <<< 1792) +
      (0x40000000000 <<< 1856)),
    ((0x8800 <<< 832) +
      (0x40000 <<< 1600) +
      (0x4 <<< 1664)),
    ((0x2200000000 <<< 768) +
      (0x2000000000000 <<< 1344) +
      (0x20 <<< 1472)),
    0,
    ((0x1080000 <<< 192) +
      (0x40200000000 <<< 448) +
      (0x100000000 <<< 1728) +
      (0x40000 <<< 1984)),
    ((0x2040000 <<< 192) +
      (0x108 <<< 704) +
      (0x200000000000 <<< 1408) +
      (0x1000000000000000 <<< 1920)),
    ((0x20400000000 <<< 448) +
      (0x402 <<< 704)),
    ((0x8010000 <<< 192) +
      (0x80100000000 <<< 448) +
      (0x204 <<< 704) +
      (0x200000000000 <<< 1024) +
      (0x8000 <<< 1792)),
    ((0x2100000000000000 <<< 128) +
      (0x21000000000000 <<< 256) +
      (0x400000000000000 <<< 1536) +
      (0x4000000000000 <<< 1920)),
    ((0x800000000 <<< 1408) +
      (0x400000000000 <<< 1728)),
    ((0x84000000000000 <<< 128) +
      (0x2100000000000000 <<< 576) +
      (0x80000 <<< 1280) +
      (0x10000000 <<< 1984)),
    ((0x21000000000000 <<< 128) +
      (0x8 <<< 1088) +
      (0x10 <<< 1472) +
      (0x8 <<< 1664) +
      (0x2 <<< 1792)),
    ((0x140000000000 <<< 64) +
      (0x28000000 <<< 512) +
      (0x4000000 <<< 1152) +
      (0x8000000000000 <<< 1344) +
      (0x4 <<< 1792)),
    ((0x100000000 <<< 1024) +
      (0x80 <<< 1472) +
      (0x10000 <<< 1600)),
    ((0x2800 <<< 384) +
      (0x140000 <<< 512) +
      (0x1 <<< 1088)),
    ((0x14000000 <<< 512) +
      (0x10000 <<< 1280)),
    ((0x42d0000000000000 <<< 960) +
      (0x4000000000 <<< 1024) +
      (0x40 <<< 1088) +
      (0x10000000 <<< 1152) +
      (0x100000000000000 <<< 1216) +
      (0x20000000000000 <<< 1344) +
      (0x2 <<< 1472) +
      (0x400000 <<< 1600) +
      (0x40 <<< 1664) +
      (0x10 <<< 1792) +
      (0x400000000000 <<< 1856)),
    ((0x42d0000000000000 <<< 960) +
      (0x4000000000 <<< 1024) +
      (0x40 <<< 1088) +
      (0x10000000 <<< 1152) +
      (0x100000000000000 <<< 1216) +
      (0x20000000000000 <<< 1344) +
      (0x2 <<< 1472) +
      (0x400000 <<< 1600) +
      (0x40 <<< 1664) +
      (0x10 <<< 1792) +
      (0x400000000000 <<< 1856)),
    0,
    ((0x4000000000000 <<< 960) +
      (0x400000 <<< 1280) +
      (0x4000000000 <<< 1408) +
      (0x8000000000000000 <<< 1536) +
      (0x80000000000 <<< 1728) +
      (0x80000000000000 <<< 1920) +
      (0x2000000 <<< 1984)),
    ((0x20020000 <<< 320) +
      (0x8000000000000 <<< 1536)),
    (0x4004 +
      (0x10010000 <<< 320) +
      (0x10000000000000 <<< 1216) +
      (0x4000000 <<< 1600) +
      (0x100 <<< 1792)),
    ((0x40000000000 <<< 1024) +
      (0x200000000000000 <<< 1344) +
      (0x400 <<< 1664)),
    ((0x80080000 <<< 320) +
      (0x400400000000 <<< 640) +
      (0x400 <<< 1088))]

/-- The high bit plane of the original preferred quarter numerators. -/
def generatedSixthMiddleOddHighMasks : Fin 24 → ℕ :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ((0x4000000000000 <<< 960)),
    ((0x4000000000000 <<< 960)),
    0,
    ((0x42d0000000000000 <<< 960) +
      (0x4000000000 <<< 1024) +
      (0x40 <<< 1088) +
      (0x10000000 <<< 1152) +
      (0x100000000000000 <<< 1216) +
      (0x400000 <<< 1280) +
      (0x20000000000000 <<< 1344) +
      (0x4000000000 <<< 1408) +
      (0x2 <<< 1472) +
      (0x8000000000000000 <<< 1536) +
      (0x400000 <<< 1600) +
      (0x40 <<< 1664) +
      (0x80000000000 <<< 1728) +
      (0x10 <<< 1792) +
      (0x400000000000 <<< 1856) +
      (0x80000000000000 <<< 1920) +
      (0x2000000 <<< 1984)),
    0,
    0,
    0,
    0]

/-- The exact executable integer numerator at every ordinary odd-short address. -/
def generatedSixthMiddleOddPackedNumerator (d : Fin 2048) (i : Fin 24) : ℤ :=
  ((if (generatedSixthMiddleOddPositiveMasks i).testBit d.val then 1 else 0) -
    (if (generatedSixthMiddleOddNegativeMasks i).testBit d.val then 1 else 0)) *
      (if (generatedSixthMiddleOddHighMasks i).testBit d.val then 3 else 1)

set_option maxHeartbeats 4000000 in
-- Check every original listed preferred coefficient against the compact signed bit planes.
/-- Every listed genuine output has its exact checked executable numerator. -/
theorem generatedSixth_middle_odd_packed_value : ∀ k : Fin 276,
    generatedSixthMiddleOddPackedNumerator
      (generatedSixthMiddleOddTargetCoordinates k).1
      (generatedSixthMiddleOddTargetCoordinates k).2 =
        generatedSixthMiddleOddCoefficientNumerator k := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Exhaust all 49,152 odd-short addresses; only displayed original outputs can be nonzero.
/-- The compact bit planes have no extra support outside the genuine complete output list. -/
theorem generatedSixth_middle_odd_packed_support : ∀ d : Fin 2048, ∀ i : Fin 24,
    generatedSixthMiddleOddPackedNumerator d i ≠ 0 →
      ∃ k : Fin 276, generatedSixthMiddleOddTargetCoordinates k = (d, i) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
