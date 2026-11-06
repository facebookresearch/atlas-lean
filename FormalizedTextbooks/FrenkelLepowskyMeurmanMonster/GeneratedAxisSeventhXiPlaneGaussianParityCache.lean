/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianPackedAction

/-! A complete ordinary-kernel parity table for original twelve-bit Pauli phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original twelve-bit parity function stored as a complete bit table. -/
def generatedSeventhXiGaussianParityBits : ℕ :=
  0x6996966996696996966969966996966996696996699696696996966996696996 +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 256) +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 512) +
  (0x6996966996696996966969966996966996696996699696696996966996696996 <<< 768) +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 1024) +
  (0x6996966996696996966969966996966996696996699696696996966996696996 <<< 1280) +
  (0x6996966996696996966969966996966996696996699696696996966996696996 <<< 1536) +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 1792) +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 2048) +
  (0x6996966996696996966969966996966996696996699696696996966996696996 <<< 2304) +
  (0x6996966996696996966969966996966996696996699696696996966996696996 <<< 2560) +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 2816) +
  (0x6996966996696996966969966996966996696996699696696996966996696996 <<< 3072) +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 3328) +
  (0x9669699669969669699696699669699669969669966969969669699669969669 <<< 3584) +
  (0x6996966996696996966969966996966996696996699696696996966996696996 <<< 3840)

/-- The integral parity sign read from the complete original binary table. -/
def generatedSeventhXiGaussianParitySign (n : ℕ) : ℤ :=
  if generatedSeventhXiGaussianParityBits.testBit n then -1 else 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every twelve-bit input is retained in the source parity certificate.
/-- Every cached parity sign equals the original complete bit-parity formula. -/
theorem generatedSeventhXiGaussianParitySign_actual : ∀ n : Fin 4096,
    generatedSeventhXiGaussianParitySign n.val =
      (if monsterNortonBitParity n.val then -1 else 1) := by
  decide +kernel

/-- Fast lookup retains every actual modulation bit and its complete central sign. -/
def generatedSeventhXiGaussianFastPhase (a : Fin 64) (d : Fin 4096) : ℤ :=
  generatedSeventhXiGaussianPackedCentral a *
    generatedSeventhXiGaussianParitySign (generatedSeventhXiGaussianPackedModulation a &&& d.val)

/-- The cached phase is exactly the full original phase at every input label. -/
theorem generatedSeventhXiGaussianFastPhase_actual (a : Fin 64) (d : Fin 4096) :
    generatedSeventhXiGaussianFastPhase a d = generatedSeventhXiGaussianPackedPhase a d := by
  have hb : generatedSeventhXiGaussianPackedModulation a &&& d.val < 4096 :=
    lt_of_le_of_lt Nat.and_le_right d.isLt
  simp only [generatedSeventhXiGaussianFastPhase, generatedSeventhXiGaussianPackedPhase,
    generatedSeventhXiGaussianParitySign_actual ⟨_, hb⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
