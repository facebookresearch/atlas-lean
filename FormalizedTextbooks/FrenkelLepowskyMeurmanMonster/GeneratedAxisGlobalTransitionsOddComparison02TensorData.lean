/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinMasks

/-! Complete candidate physical tensor factors for the original comparison word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every positive original physical spin coordinate. -/
def generatedAxisGlobalOddComparison02SpinPositive : Fin 16 → ℕ :=
  ![0x66000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x600609900000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x90090000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- Every negative original physical spin coordinate. -/
def generatedAxisGlobalOddComparison02SpinNegative : Fin 16 → ℕ :=
  ![0x90090000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x66000000000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x600609900000,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The complete signed physical spin numerator. -/
def generatedAxisGlobalOddComparison02Spin : Fin 4096 → ℤ :=
  generatedAxisGlobalOddMaskedSpin generatedAxisGlobalOddComparison02SpinPositive
    generatedAxisGlobalOddComparison02SpinNegative 4

/-- The complete original spatial numerator. -/
def generatedAxisGlobalOddComparison02Spatial : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, -1, -1, 0]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
