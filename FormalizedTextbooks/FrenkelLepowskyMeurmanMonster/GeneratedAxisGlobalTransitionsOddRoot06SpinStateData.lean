/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinMasks

/-! Complete candidate integer factors of the original phase-preserving source word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All physical positive spin coordinates after source primitive 0. -/
def generatedAxisGlobalOddRoot06Spin00Positive : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x1,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- All physical negative spin coordinates after source primitive 0. -/
def generatedAxisGlobalOddRoot06Spin00Negative : Fin 16 → ℕ :=
  ![0x1,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The complete signed candidate spin vector after primitive 0. -/
def generatedAxisGlobalOddRoot06Spin00 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin00Positive
    generatedAxisGlobalOddRoot06Spin00Negative 8

/-- The original physical spatial numerator after primitive 0. -/
def generatedAxisGlobalOddRoot06Spatial00 : Fin 24 → ℤ :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All physical positive spin coordinates after source primitive 1. -/
def generatedAxisGlobalOddRoot06Spin01Positive : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x0,
    0x8117,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x8117,
    0x0,
    0x0,
    0x0]

/-- All physical negative spin coordinates after source primitive 1. -/
def generatedAxisGlobalOddRoot06Spin01Negative : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x0,
    0x7ee8,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x7ee8,
    0x0,
    0x0,
    0x0]

/-- The complete signed candidate spin vector after primitive 1. -/
def generatedAxisGlobalOddRoot06Spin01 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin01Positive
    generatedAxisGlobalOddRoot06Spin01Negative 2

/-- The original physical spatial numerator after primitive 1. -/
def generatedAxisGlobalOddRoot06Spatial01 : Fin 24 → ℤ :=
  ![-1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All physical positive spin coordinates after source primitive 2. -/
def generatedAxisGlobalOddRoot06Spin02Positive : Fin 16 → ℕ :=
  ![0x200800000000000000000000,
    0x0,
    0x0,
    0x200800000000000000000000,
    0x100400000000000000000000,
    0x0,
    0x0,
    0x100400000000000000000000,
    0x200800000000000000000000,
    0x0,
    0x0,
    0x200800000000000000000000,
    0x100400000000000000000000,
    0x0,
    0x0,
    0x100400000000000000000000]

/-- All physical negative spin coordinates after source primitive 2. -/
def generatedAxisGlobalOddRoot06Spin02Negative : Fin 16 → ℕ :=
  ![0x0,
    0x200800000000000000000000,
    0x200800000000000000000000,
    0x0,
    0x0,
    0x100400000000000000000000,
    0x100400000000000000000000,
    0x0,
    0x0,
    0x200800000000000000000000,
    0x200800000000000000000000,
    0x0,
    0x0,
    0x100400000000000000000000,
    0x100400000000000000000000,
    0x0]

/-- The complete signed candidate spin vector after primitive 2. -/
def generatedAxisGlobalOddRoot06Spin02 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin02Positive
    generatedAxisGlobalOddRoot06Spin02Negative 2

/-- The original physical spatial numerator after primitive 2. -/
def generatedAxisGlobalOddRoot06Spatial02 : Fin 24 → ℤ :=
  ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0]

/-- All physical positive spin coordinates after source primitive 3. -/
def generatedAxisGlobalOddRoot06Spin03Positive : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x0,
    0x44000000000200800000000000000000000000000000000000000000000,
    0x5000000000aa000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x44000000000200800000000000000000000000000000000000000000000,
    0x5000000000aa000000000000000000000000000000000000000000000,
    0x0,
    0x0]

/-- All physical negative spin coordinates after source primitive 3. -/
def generatedAxisGlobalOddRoot06Spin03Negative : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x0,
    0x11000000000800200000000000000000000000000000000000000000000,
    0x500000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x11000000000800200000000000000000000000000000000000000000000,
    0x500000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0]

/-- The complete signed candidate spin vector after primitive 3. -/
def generatedAxisGlobalOddRoot06Spin03 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin03Positive
    generatedAxisGlobalOddRoot06Spin03Negative 2

/-- The original physical spatial numerator after primitive 3. -/
def generatedAxisGlobalOddRoot06Spatial03 : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0]

/-- All physical positive spin coordinates after source primitive 4. -/
def generatedAxisGlobalOddRoot06Spin04Positive : Fin 16 → ℕ :=
  ![0x0,
    0xaa000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0xaa000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- All physical negative spin coordinates after source primitive 4. -/
def generatedAxisGlobalOddRoot06Spin04Negative : Fin 16 → ℕ :=
  ![0xa00a00000000055000000000000000000000000000000000000000000000,
    0x500500000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0xa00a00000000055000000000000000000000000000000000000000000000,
    0x500500000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The complete signed candidate spin vector after primitive 4. -/
def generatedAxisGlobalOddRoot06Spin04 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin04Positive
    generatedAxisGlobalOddRoot06Spin04Negative 2

/-- The original physical spatial numerator after primitive 4. -/
def generatedAxisGlobalOddRoot06Spatial04 : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1, 0, 1]

/-- All physical positive spin coordinates after source primitive 5. -/
def generatedAxisGlobalOddRoot06Spin05Positive : Fin 16 → ℕ :=
  ![0x400100000000100100000000000000000000000000000000000000000000,
    0x500000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x100400000000400400000000000000000000000000000000000000000000,
    0x500500000000500000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- All physical negative spin coordinates after source primitive 5. -/
def generatedAxisGlobalOddRoot06Spin05Negative : Fin 16 → ℕ :=
  ![0x100400000000400400000000000000000000000000000000000000000000,
    0x500500000000500000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x400100000000100100000000000000000000000000000000000000000000,
    0x500000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The complete signed candidate spin vector after primitive 5. -/
def generatedAxisGlobalOddRoot06Spin05 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin05Positive
    generatedAxisGlobalOddRoot06Spin05Negative 2

/-- The original physical spatial numerator after primitive 5. -/
def generatedAxisGlobalOddRoot06Spatial05 : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0]

/-- All physical positive spin coordinates after source primitive 6. -/
def generatedAxisGlobalOddRoot06Spin06Positive : Fin 16 → ℕ :=
  ![0x900980010000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x980080000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x10080000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x900010010000,
    0x0,
    0x0,
    0x0,
    0x0]

/-- All physical negative spin coordinates after source primitive 6. -/
def generatedAxisGlobalOddRoot06Spin06Negative : Fin 16 → ℕ :=
  ![0x10080000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x900010010000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x900980010000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x980080000,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The complete signed candidate spin vector after primitive 6. -/
def generatedAxisGlobalOddRoot06Spin06 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin06Positive
    generatedAxisGlobalOddRoot06Spin06Negative 2

/-- The original physical spatial numerator after primitive 6. -/
def generatedAxisGlobalOddRoot06Spatial06 : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, -1]

/-- All physical positive spin coordinates after source primitive 7. -/
def generatedAxisGlobalOddRoot06Spin07Positive : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x0,
    0x100806600000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x88000060000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x100806600000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x88000060000]

/-- All physical negative spin coordinates after source primitive 7. -/
def generatedAxisGlobalOddRoot06Spin07Negative : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x0,
    0x800100000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x11060000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x800100000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x11060000000]

/-- The complete signed candidate spin vector after primitive 7. -/
def generatedAxisGlobalOddRoot06Spin07 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin07Positive
    generatedAxisGlobalOddRoot06Spin07Negative 2

/-- The original physical spatial numerator after primitive 7. -/
def generatedAxisGlobalOddRoot06Spatial07 : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1]

/-- All physical positive spin coordinates after source primitive 8. -/
def generatedAxisGlobalOddRoot06Spin08Positive : Fin 16 → ℕ :=
  ![0x0,
    0x0,
    0x0,
    0x9900000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x9900000,
    0x0,
    0x0,
    0x0,
    0x0]

/-- All physical negative spin coordinates after source primitive 8. -/
def generatedAxisGlobalOddRoot06Spin08Negative : Fin 16 → ℕ :=
  ![0x66090090000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x600600000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x66090090000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x600600000000,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The complete signed candidate spin vector after primitive 8. -/
def generatedAxisGlobalOddRoot06Spin08 : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddRoot06Spin08Positive
    generatedAxisGlobalOddRoot06Spin08Negative 2

/-- The original physical spatial numerator after primitive 8. -/
def generatedAxisGlobalOddRoot06Spatial08 : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1, 1, 0]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
