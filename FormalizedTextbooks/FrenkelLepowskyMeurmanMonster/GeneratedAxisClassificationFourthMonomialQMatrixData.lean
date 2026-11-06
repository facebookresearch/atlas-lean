/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortHom
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQImage

/-! Finite full-Q matrices for the actual corrected original monomial words. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Candidate binary row masks, to be bound to actual spin conjugation on every basis lift. -/
def generatedFourthMonomialQBinaryRows : Fin 4 → Fin 24 → ℕ :=
  ![
    ![1089, 1090, 946, 1096, 16, 241, 145, 1041,
      1629, 1771, 1233, 2919, 16651544, 10511116, 9437258, 3180503,
      6242633, 10633408, 15904828, 6702376, 8405147, 11551754, 7910025, 8388608],
    ![1073, 2, 1752, 1508, 1056, 1040, 128, 64,
      1536, 1280, 1024, 3840, 4912, 9984, 33232, 17120,
      151685, 102473, 575020, 312604, 10519687, 9454667, 15979458, 8388608],
    ![1, 527, 2034, 1362, 177, 32, 97, 128,
      1654, 172, 1185, 2048, 4535938, 1106593, 3154848, 2105760,
      1163776, 7816974, 1360384, 6898959, 49324, 1074295, 5292705, 8388608],
    ![1073, 1362, 4, 1896, 1040, 1056, 64, 128,
      1280, 512, 1024, 3584, 4656, 9040, 17920, 33120,
      77955, 168137, 304426, 524848, 1089610, 10519687, 13873732, 8388608]
  ]

/-- Candidate full central phase masks, including the diagonal central terms. -/
def generatedFourthMonomialQPhaseRows : Fin 4 → Fin 24 → ℕ :=
  ![
    ![1749, 1868, 156, 840, 1728, 1152, 1856, 1664,
      256, 1024, 1024, 0, 4096, 0, 0, 0,
      0, 0, 0, 524288, 1048576, 0, 0, 0],
    ![816, 1792, 740, 464, 672, 352, 1536, 1280,
      1536, 1536, 0, 0, 4096, 8192, 16384, 0,
      65536, 131072, 0, 0, 0, 0, 0, 0],
    ![1667, 12, 1660, 1744, 160, 704, 192, 512,
      512, 512, 0, 0, 0, 8192, 0, 0,
      0, 0, 0, 0, 1048576, 0, 0, 0],
    ![561, 850, 1540, 360, 480, 928, 1856, 640,
      768, 1536, 0, 0, 4096, 0, 0, 0,
      65536, 131072, 0, 0, 1048576, 0, 0, 0]
  ]

/-- Literal binary matrix specified by the finite candidate row masks. -/
def generatedFourthMonomialQBinaryMatrix (k : Fin 4) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((generatedFourthMonomialQBinaryRows k i).testBit j.val)

/-- Literal central matrix specified by the finite candidate masks. -/
def generatedFourthMonomialQPhaseMatrix (k : Fin 4) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((generatedFourthMonomialQPhaseRows k i).testBit j.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check four times576 actual extraspecial cocycle identities on coordinate pairs.
/-- Every candidate pair of matrices satisfies the genuine extraspecial cocycle identity. -/
theorem generatedFourth_monomial_q_matrix_cocycles : ∀ k : Fin 4, ∀ i j : Fin 24,
    qBeta (generatedFourthMonomialQBinaryMatrix k *ᵥ Pi.single i 1)
      (generatedFourthMonomialQBinaryMatrix k *ᵥ Pi.single j 1) =
        qBeta (Pi.single i 1) (Pi.single j 1) +
          generatedFourthMonomialQPhaseMatrix k i j +
          generatedFourthMonomialQPhaseMatrix k j i := by
  decide +kernel

/-- The certified cocycle matrices define a genuine homomorphism on the original Q group. -/
def generatedFourthMonomialQMatrixHom (k : Fin 4) : Q →* Q :=
  generatedFourthLiftQMatrixHom (generatedFourthMonomialQBinaryMatrix k)
    (generatedFourthMonomialQPhaseMatrix k) (generatedFourth_monomial_q_matrix_cocycles k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
