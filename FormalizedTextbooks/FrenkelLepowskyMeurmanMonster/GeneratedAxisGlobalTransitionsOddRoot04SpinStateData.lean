/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinMasks

/-! Exact complete dyadic factors for every original root-four source stage. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- All original positive physical spin labels at stage 0. -/
def generatedAxisGlobalOddRoot04Spin00Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 0. -/
def generatedAxisGlobalOddRoot04Spin00Negative : Fin 16 → ℕ := ![0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 0. -/
def generatedAxisGlobalOddRoot04Spin00 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin00Positive
    generatedAxisGlobalOddRoot04Spin00Negative 8

/-- Complete original spatial numerator at stage 0. -/
def generatedAxisGlobalOddRoot04Spatial00 : Fin 24 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 1. -/
def generatedAxisGlobalOddRoot04Spin01Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 1. -/
def generatedAxisGlobalOddRoot04Spin01Negative : Fin 16 → ℕ := ![0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 1. -/
def generatedAxisGlobalOddRoot04Spin01 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin01Positive
    generatedAxisGlobalOddRoot04Spin01Negative 8

/-- Complete original spatial numerator at stage 1. -/
def generatedAxisGlobalOddRoot04Spatial01 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 2. -/
def generatedAxisGlobalOddRoot04Spin02Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x10000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 2. -/
def generatedAxisGlobalOddRoot04Spin02Negative : Fin 16 → ℕ := ![0x10000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 2. -/
def generatedAxisGlobalOddRoot04Spin02 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin02Positive
    generatedAxisGlobalOddRoot04Spin02Negative 8

/-- Complete original spatial numerator at stage 2. -/
def generatedAxisGlobalOddRoot04Spatial02 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 3. -/
def generatedAxisGlobalOddRoot04Spin03Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x800000000000000, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 3. -/
def generatedAxisGlobalOddRoot04Spin03Negative : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x800000000000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 3. -/
def generatedAxisGlobalOddRoot04Spin03 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin03Positive
    generatedAxisGlobalOddRoot04Spin03Negative 8

/-- Complete original spatial numerator at stage 3. -/
def generatedAxisGlobalOddRoot04Spatial03 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

/-- All original positive physical spin labels at stage 4. -/
def generatedAxisGlobalOddRoot04Spin04Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x100, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 4. -/
def generatedAxisGlobalOddRoot04Spin04Negative : Fin 16 → ℕ := ![0x0, 0x100, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 4. -/
def generatedAxisGlobalOddRoot04Spin04 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin04Positive
    generatedAxisGlobalOddRoot04Spin04Negative 8

/-- Complete original spatial numerator at stage 4. -/
def generatedAxisGlobalOddRoot04Spatial04 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 5. -/
def generatedAxisGlobalOddRoot04Spin05Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 5. -/
def generatedAxisGlobalOddRoot04Spin05Negative : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 5. -/
def generatedAxisGlobalOddRoot04Spin05 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin05Positive
    generatedAxisGlobalOddRoot04Spin05Negative 8

/-- Complete original spatial numerator at stage 5. -/
def generatedAxisGlobalOddRoot04Spatial05 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 6. -/
def generatedAxisGlobalOddRoot04Spin06Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x10000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- All original negative physical spin labels at stage 6. -/
def generatedAxisGlobalOddRoot04Spin06Negative : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x10000, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- Complete original physical spin numerator at stage 6. -/
def generatedAxisGlobalOddRoot04Spin06 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin06Positive
    generatedAxisGlobalOddRoot04Spin06Negative 8

/-- Complete original spatial numerator at stage 6. -/
def generatedAxisGlobalOddRoot04Spatial06 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 7. -/
def generatedAxisGlobalOddRoot04Spin07Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x7ee80000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x7ee80000, 0x0]

/-- All original negative physical spin labels at stage 7. -/
def generatedAxisGlobalOddRoot04Spin07Negative : Fin 16 → ℕ := ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x81170000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x81170000, 0x0]

/-- Complete original physical spin numerator at stage 7. -/
def generatedAxisGlobalOddRoot04Spin07 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin07Positive
    generatedAxisGlobalOddRoot04Spin07Negative 2

/-- Complete original spatial numerator at stage 7. -/
def generatedAxisGlobalOddRoot04Spatial07 : Fin 24 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 8. -/
def generatedAxisGlobalOddRoot04Spin08Positive : Fin 16 → ℕ := ![0x0, 0x0, 0x2200000000000000000000000000000, 0x0, 0x0, 0x0, 0x20020000000000000000000000000000, 0x0, 0x0, 0x0, 0x2200000000000000000000000000000, 0x0, 0x0, 0x0, 0x20020000000000000000000000000000, 0x0]

/-- All original negative physical spin labels at stage 8. -/
def generatedAxisGlobalOddRoot04Spin08Negative : Fin 16 → ℕ := ![0x2200000000000000000000000000000000000000000000000000000, 0x22000000000000000000000000000000000, 0x0, 0x22000000000, 0x20020000000000000000000000000000000000000000000000000000, 0x200200000000000000000000000000000000, 0x0, 0x200200000000, 0x2200000000000000000000000000000000000000000000000000000, 0x22000000000000000000000000000000000, 0x0, 0x22000000000, 0x20020000000000000000000000000000000000000000000000000000, 0x200200000000000000000000000000000000, 0x0, 0x200200000000]

/-- Complete original physical spin numerator at stage 8. -/
def generatedAxisGlobalOddRoot04Spin08 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin08Positive
    generatedAxisGlobalOddRoot04Spin08Negative 2

/-- Complete original spatial numerator at stage 8. -/
def generatedAxisGlobalOddRoot04Spatial08 : Fin 24 → ℤ := ![0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All original positive physical spin labels at stage 9. -/
def generatedAxisGlobalOddRoot04Spin09Positive : Fin 16 → ℕ := ![0xcc00000000000000000000000000000000000000000000000000000, 0xcc000000000000000000000000000000000, 0x3300000000000000000000000000000, 0xcc000000000, 0x500a0000000000000000000000000000000000000000000000000000, 0x500a00000000000000000000000000000000, 0xa0050000000000000000000000000000, 0x500a00000000, 0x3300000000000000000000000000000000000000000000000000000, 0x33000000000000000000000000000000000, 0xcc00000000000000000000000000000, 0x33000000000, 0x500a0000000000000000000000000000000000000000000000000000, 0x500a00000000000000000000000000000000, 0xa0050000000000000000000000000000, 0x500a00000000]

/-- All original negative physical spin labels at stage 9. -/
def generatedAxisGlobalOddRoot04Spin09Negative : Fin 16 → ℕ := ![0x3300000000000000000000000000000000000000000000000000000, 0x33000000000000000000000000000000000, 0xcc00000000000000000000000000000, 0x33000000000, 0xa0050000000000000000000000000000000000000000000000000000, 0xa00500000000000000000000000000000000, 0x500a0000000000000000000000000000, 0xa00500000000, 0xcc00000000000000000000000000000000000000000000000000000, 0xcc000000000000000000000000000000000, 0x3300000000000000000000000000000, 0xcc000000000, 0xa0050000000000000000000000000000000000000000000000000000, 0xa00500000000000000000000000000000000, 0x500a0000000000000000000000000000, 0xa00500000000]

/-- Complete original physical spin numerator at stage 9. -/
def generatedAxisGlobalOddRoot04Spin09 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot04Spin09Positive
    generatedAxisGlobalOddRoot04Spin09Negative 1

/-- Complete original spatial numerator at stage 9. -/
def generatedAxisGlobalOddRoot04Spatial09 : Fin 24 → ℤ := ![1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
