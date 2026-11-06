/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinMasks

/-! Exact complete dyadic factors for every original root-2 source stage. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- All original positive physical spin labels at stage 0. -/
def generatedAxisGlobalOddRoot02Spin00Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 0. -/
def generatedAxisGlobalOddRoot02Spin00Negative : Fin 16 → ℕ := ![0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 0. -/
def generatedAxisGlobalOddRoot02Spin00 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin00Positive
    generatedAxisGlobalOddRoot02Spin00Negative 8

/-- Complete original spatial numerator at stage 0. -/
def generatedAxisGlobalOddRoot02Spatial00 : Fin 24 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 1. -/
def generatedAxisGlobalOddRoot02Spin01Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 1. -/
def generatedAxisGlobalOddRoot02Spin01Negative : Fin 16 → ℕ := ![0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 1. -/
def generatedAxisGlobalOddRoot02Spin01 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin01Positive
    generatedAxisGlobalOddRoot02Spin01Negative 8

/-- Complete original spatial numerator at stage 1. -/
def generatedAxisGlobalOddRoot02Spatial01 : Fin 24 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 2. -/
def generatedAxisGlobalOddRoot02Spin02Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 2. -/
def generatedAxisGlobalOddRoot02Spin02Negative : Fin 16 → ℕ := ![0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 2. -/
def generatedAxisGlobalOddRoot02Spin02 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin02Positive
    generatedAxisGlobalOddRoot02Spin02Negative 8

/-- Complete original spatial numerator at stage 2. -/
def generatedAxisGlobalOddRoot02Spatial02 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 3. -/
def generatedAxisGlobalOddRoot02Spin03Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 3. -/
def generatedAxisGlobalOddRoot02Spin03Negative : Fin 16 → ℕ := ![0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 3. -/
def generatedAxisGlobalOddRoot02Spin03 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin03Positive
    generatedAxisGlobalOddRoot02Spin03Negative 8

/-- Complete original spatial numerator at stage 3. -/
def generatedAxisGlobalOddRoot02Spatial03 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 4. -/
def generatedAxisGlobalOddRoot02Spin04Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x8117, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8117, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 4. -/
def generatedAxisGlobalOddRoot02Spin04Negative : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x7ee8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x7ee8, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 4. -/
def generatedAxisGlobalOddRoot02Spin04 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin04Positive
    generatedAxisGlobalOddRoot02Spin04Negative 2

/-- Complete original spatial numerator at stage 4. -/
def generatedAxisGlobalOddRoot02Spatial04 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 5. -/
def generatedAxisGlobalOddRoot02Spin05Positive : Fin 16 → ℕ := ![0x2008, 0x0, 0x0, 0x2008, 0x4001000000000000000000000000000000000000000000000000000000000000, 0x1004000000000000000000000000000000000000000000000000000000000000, 0x1004000000000000000000000000000000000000000000000000000000000000, 0x4001000000000000000000000000000000000000000000000000000000000000, 0x2008, 0x0, 0x0, 0x2008, 0x4001000000000000000000000000000000000000000000000000000000000000, 0x1004000000000000000000000000000000000000000000000000000000000000, 0x1004000000000000000000000000000000000000000000000000000000000000, 0x4001000000000000000000000000000000000000000000000000000000000000]

/-- All original negative physical spin labels at stage 5. -/
def generatedAxisGlobalOddRoot02Spin05Negative : Fin 16 → ℕ := ![0x0, 0x8002, 0x8002, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8002, 0x8002, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 5. -/
def generatedAxisGlobalOddRoot02Spin05 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin05Positive
    generatedAxisGlobalOddRoot02Spin05Negative 2

/-- Complete original spatial numerator at stage 5. -/
def generatedAxisGlobalOddRoot02Spatial05 : Fin 24 → ℤ := ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0]

/-- All original positive physical spin labels at stage 6. -/
def generatedAxisGlobalOddRoot02Spin06Positive : Fin 16 → ℕ := ![0x0, 0x2000000000000000100000000000000000000, 0x10000000000000002000000000000000000000000, 0x0, 0x1000000000000000000000000000000000000000000000002000000000000, 0x0, 0x0, 0x2000000000000000000000000000000000000000000000001, 0x0, 0x2000000000000000100000000000000000000, 0x10000000000000002000000000000000000000000, 0x0, 0x1000000000000000000000000000000000000000000000002000000000000, 0x0, 0x0, 0x2000000000000000000000000000000000000000000000001]

/-- All original negative physical spin labels at stage 6. -/
def generatedAxisGlobalOddRoot02Spin06Negative : Fin 16 → ℕ := ![0x0, 0x40000000000000008000000000000000000000000000, 0x8000000000000000400000000000000000000000, 0x0, 0x8000000000000000000000000000000000000000000000004000, 0x0, 0x0, 0x4000000000000000000000000000000000000000000000008000000000000000, 0x0, 0x40000000000000008000000000000000000000000000, 0x8000000000000000400000000000000000000000, 0x0, 0x8000000000000000000000000000000000000000000000004000, 0x0, 0x0, 0x4000000000000000000000000000000000000000000000008000000000000000]

/-- Complete original physical spin numerator at stage 6. -/
def generatedAxisGlobalOddRoot02Spin06 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin06Positive
    generatedAxisGlobalOddRoot02Spin06Negative 2

/-- Complete original spatial numerator at stage 6. -/
def generatedAxisGlobalOddRoot02Spatial06 : Fin 24 → ℤ := ![-1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0]

/-- All original positive physical spin labels at stage 7. -/
def generatedAxisGlobalOddRoot02Spin07Positive : Fin 16 → ℕ := ![0x0, 0xa0000000000000000, 0x0, 0x0, 0x200000000000000000000200000000000000000100000000000000000000004, 0x0, 0x0, 0x0, 0x0, 0xa0000000000000000, 0x0, 0x0, 0x200000000000000000000200000000000000000100000000000000000000004, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 7. -/
def generatedAxisGlobalOddRoot02Spin07Negative : Fin 16 → ℕ := ![0x0, 0x50000000000500000000000000000000000000000000000000a0000000, 0x0, 0x0, 0x800000000000000000000800000000000000000400000000000000000000001, 0x0, 0x0, 0x0, 0x0, 0x50000000000500000000000000000000000000000000000000a0000000, 0x0, 0x0, 0x800000000000000000000800000000000000000400000000000000000000001, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 7. -/
def generatedAxisGlobalOddRoot02Spin07 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin07Positive
    generatedAxisGlobalOddRoot02Spin07Negative 2

/-- Complete original spatial numerator at stage 7. -/
def generatedAxisGlobalOddRoot02Spatial07 : Fin 24 → ℤ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 8. -/
def generatedAxisGlobalOddRoot02Spin08Positive : Fin 16 → ℕ := ![0xa0500000000000000000a5000000000000000000a00a0000000000000000a55a, 0x0, 0x0, 0x0, 0x0, 0x241800000000214800000000000000000000000081180000000084480000, 0x0, 0x0, 0x50a0000000000000000005a0000000000000000055000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x241800000000214800000000000000000000000081180000000084480000, 0x0, 0x0]

/-- All original negative physical spin labels at stage 8. -/
def generatedAxisGlobalOddRoot02Spin08Negative : Fin 16 → ℕ := ![0x50a0000000000000000005a0000000000000000055000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x814200000000841200000000000000000000000024420000000021120000, 0x0, 0x0, 0xa0500000000000000000a5000000000000000000a00a0000000000000000a55a, 0x0, 0x0, 0x0, 0x0, 0x814200000000841200000000000000000000000024420000000021120000, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 8. -/
def generatedAxisGlobalOddRoot02Spin08 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin08Positive
    generatedAxisGlobalOddRoot02Spin08Negative 1

/-- Complete original spatial numerator at stage 8. -/
def generatedAxisGlobalOddRoot02Spatial08 : Fin 24 → ℤ := ![-1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 3, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 9. -/
def generatedAxisGlobalOddRoot02Spin09Positive : Fin 16 → ℕ := ![0x80000800000000000000000000000000000000000000000000008800000, 0x1001000000001000000100000000000000000000, 0x11000000000000000100100000000000000000000, 0x88000000000000000000000000000000000000000000000080000800000, 0x10000000000100000000000000000000000000000000000000000000000110, 0x800800000000000080000000000000080000000000000000, 0x800000000800080080000000000000000000000000000, 0x110000000000000000000000000000000000000000000000010000000000100, 0x80000800000000000000000000000000000000000000000000008800000, 0x10010000000000000001100000000000000000000000, 0x10000001000000001001000000000000000000000000, 0x88000000000000000000000000000000000000000000000080000800000, 0x100000000000010000000000000000000000000000000000110000000000000, 0x800800000000000080000000000000080000000000000000, 0x800000000800080080000000000000000000000000000, 0x110000000000000000000000000000000000100000000000010]

/-- All original negative physical spin labels at stage 9. -/
def generatedAxisGlobalOddRoot02Spin09Negative : Fin 16 → ℕ := ![0x8008000000000000000000000000000000000000000000088000000000, 0x10010000000000000001100000000000000000000000, 0x10000001000000001001000000000000000000000000, 0x8800000000000000000000000000000000000000000008008000000, 0x100000000000010000000000000000000000000000000000110000000000000, 0x800800080000000080000000000000000000, 0x800000000000000800000000000080080000000000000000, 0x110000000000000000000000000000000000100000000000010, 0x8008000000000000000000000000000000000000000000088000000000, 0x1001000000001000000100000000000000000000, 0x11000000000000000100100000000000000000000, 0x8800000000000000000000000000000000000000000008008000000, 0x10000000000100000000000000000000000000000000000000000000000110, 0x800800080000000080000000000000000000, 0x800000000000000800000000000080080000000000000000, 0x110000000000000000000000000000000000000000000000010000000000100]

/-- Complete original physical spin numerator at stage 9. -/
def generatedAxisGlobalOddRoot02Spin09 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin09Positive
    generatedAxisGlobalOddRoot02Spin09Negative 1

/-- Complete original spatial numerator at stage 9. -/
def generatedAxisGlobalOddRoot02Spatial09 : Fin 24 → ℤ := ![-1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 10. -/
def generatedAxisGlobalOddRoot02Spin10Positive : Fin 16 → ℕ := ![0x4004000000000000000000000000000000000000000000, 0x400004000000000044004400000000000000000000000000000000000000000, 0x440000000000040004000000000, 0x4000400000000000440000000000000, 0x4004000000000004000400000000000000000000000000000000, 0x40004000000000000400400000000000000000000000000000000, 0x400440040000000040000004, 0x400000040000000040044004, 0x440044000000000040000400000000000000000000000000000000000000000, 0x40040000000000000000000000000000000000000000000000000000000000, 0x440000000000040004000000000, 0x4000400000000000440000000000000, 0x4004000000000004000400000000000000000000000000000000, 0x40004000000000000400400000000000000000000000000000000, 0x44000, 0x440000000000000000000]

/-- All original negative physical spin labels at stage 10. -/
def generatedAxisGlobalOddRoot02Spin10Negative : Fin 16 → ℕ := ![0x440044000000000040000400000000000000000000000000000000000000000, 0x40040000000000000000000000000000000000000000000000000000000000, 0x4400000000000000400040000000000, 0x400040000000000000044000000000, 0x40040000000000004000400000000000000000000000000000000000, 0x40004000000000004004000000000000000000000000000000000000, 0x44000, 0x440000000000000000000, 0x4004000000000000000000000000000000000000000000, 0x400004000000000044004400000000000000000000000000000000000000000, 0x4400000000000000400040000000000, 0x400040000000000000044000000000, 0x40040000000000004000400000000000000000000000000000000000, 0x40004000000000004004000000000000000000000000000000000000, 0x400440040000000040000004, 0x400000040000000040044004]

/-- Complete original physical spin numerator at stage 10. -/
def generatedAxisGlobalOddRoot02Spin10 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin10Positive
    generatedAxisGlobalOddRoot02Spin10Negative 1

/-- Complete original spatial numerator at stage 10. -/
def generatedAxisGlobalOddRoot02Spatial10 : Fin 24 → ℤ := ![3, 1, 0, 0, -1, 1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 11. -/
def generatedAxisGlobalOddRoot02Spin11Positive : Fin 16 → ℕ := ![0x300c300c0aa0055003c00c30a00aa00a00000000000000000000000000000000, 0xc3003c0a00aa00ac003c0030aa0055000000000000000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x300cc0030550055003c003c05005a00a, 0xc300c305005a00ac003300c05500550, 0x300c300c05500aa003c00c305005500500000000000000000000000000000000, 0xc3003c050055005c003c00305500aa000000000000000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x300cc0030aa00aa003c003c0a00a5005, 0xc300c30a00a5005c003300c0aa00aa0]

/-- All original negative physical spin labels at stage 11. -/
def generatedAxisGlobalOddRoot02Spin11Negative : Fin 16 → ℕ := ![0xc003c00305500aa00c3003c05005500500000000000000000000000000000000, 0x3c00c3050055005300c300c05500aa000000000000000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0xc003300c0aa00aa00c300c30a00a5005, 0x3c003c0a00a5005300cc0030aa00aa0, 0xc003c0030aa005500c3003c0a00aa00a00000000000000000000000000000000, 0x3c00c30a00aa00a300c300c0aa0055000000000000000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0xc003300c055005500c300c305005a00a, 0x3c003c05005a00a300cc00305500550]

/-- Complete original physical spin numerator at stage 11. -/
def generatedAxisGlobalOddRoot02Spin11 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot02Spin11Positive
    generatedAxisGlobalOddRoot02Spin11Negative 1

/-- Complete original spatial numerator at stage 11. -/
def generatedAxisGlobalOddRoot02Spatial11 : Fin 24 → ℤ := ![-2, 2, 1, 1, 0, 0, -1, -1, 1, -1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
