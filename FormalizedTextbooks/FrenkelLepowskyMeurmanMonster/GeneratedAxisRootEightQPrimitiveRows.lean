/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitiveData

/-! Complete triangular central cochains for the actual root-eight primitives. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Strictly upper triangular cocycle differences of the original full binary columns. -/
def generatedRootEightQPrimitiveRows : Fin 11 → Fin 24 → ℕ :=
![![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1038, 12, 1032, 1024, 864, 896, 896, 768, 1536, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4096, 8192, 16384, 32768, 0, 0, 0, 0, 0, 0, 4194304, 8388608, 57344, 49152, 32768, 0, 0, 0, 0,
    0, 0, 0, 8388608, 0],
  ![0, 1024, 1024, 1024, 32, 0, 0, 0, 512, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![768, 240, 144, 96, 64, 128, 0, 0, 1024, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 8388608,
    0, 0],
  ![270, 92, 232, 176, 192, 64, 0, 0, 1536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 8388608,
    0],
  ![1070, 2044, 920, 1024, 736, 640, 384, 256, 512, 0, 0, 0, 0, 0, 8388608, 0, 8388608, 0, 0,
    8388608, 0, 0, 8388608, 0],
  ![1040, 0, 1504, 432, 704, 640, 128, 768, 512, 0, 0, 0, 8388608, 0, 8388608, 0, 0, 8388608, 0,
    8388608, 0, 0, 0, 0]]

set_option maxHeartbeats 64000000 in
-- Check every triangular cocycle entry in all eleven actual primitive maps.
set_option maxRecDepth 100000 in
-- Evaluate the complete finite coordinate pairing, with all original columns retained.
/-- The recorded rows are exactly the original cocycle differences on all basis pairs. -/
theorem generatedRootEight_Q_primitive_rows_actual : ∀ k : Fin 11, ∀ i j : Fin 24,
    monsterCo1GeometryBinaryMaskDecode (generatedRootEightQPrimitiveRows k i) j =
      if i < j then qBeta
        (monsterCo1GeometryBinaryMaskDecode (generatedRootEightQPrimitiveColumns k i))
        (monsterCo1GeometryBinaryMaskDecode (generatedRootEightQPrimitiveColumns k j)) +
        qBeta (Pi.single i 1) (Pi.single j 1) else 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
