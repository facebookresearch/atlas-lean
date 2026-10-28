/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialMaskQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorData

/-! Exact source rows and full Q coordinates for direct bit-parity monomial tensor checks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Literal original coordinate rows of all four completely certified spin models. -/
def generatedSixthMonomialMaskCoordinateRows : Fin 4 → Fin 12 → Fin 4096 :=
  ![![1031, 1037, 1035, 1038, 720, 864, 768, 256, 128, 192, 1024, 3087],
    ![519, 1679, 523, 1435, 1021, 79, 1464, 1466, 536, 1999, 1973, 2733],
    ![882, 979, 2038, 2035, 1088, 1940, 425, 1207, 62, 857, 1876, 3085],
    ![1706, 1699, 838, 1453, 46, 979, 889, 1566, 1152, 1216, 2004, 2971]]

/-- Literal original phase rows of all four completely certified spin models. -/
def generatedSixthMonomialMaskPhaseRows : Fin 4 → Fin 12 → Fin 4096 :=
  ![![0, 2, 4, 0, 0, 0, 256, 768, 0, 0, 1024, 0],
    ![1947, 204, 952, 72, 960, 800, 1920, 768, 512, 512, 1024, 0],
    ![542, 606, 568, 1936, 1520, 960, 1408, 256, 1792, 512, 0, 0],
    ![1793, 482, 676, 1864, 1936, 608, 1344, 1280, 1536, 512, 1024, 0]]

/-- Literal original Q translation labels, with no phase discarded. -/
def generatedSixthMonomialMaskTranslation : Fin 4 → Fin 4096 := ![2687, 3071, 3440, 1276]

/-- Literal original Q modulation labels. -/
def generatedSixthMonomialMaskModulation : Fin 4 → Fin 4096 := ![1158, 524, 513, 1866]

/-- The complete preferred central signs of the actual corrections. -/
def generatedSixthMonomialMaskCentral : Fin 4 → ZMod 2 := ![0, 1, 0, 0]

/-- Every direct coordinate-row table is the original full checked spin model. -/
theorem generatedSixth_monomial_mask_coordinate (k : Fin 4) :
    (generatedSixthMonomialSpinModel k).coordinate =
      representativeMatrix (generatedSixthMonomialMaskCoordinateRows k) := by
  fin_cases k <;> rfl

/-- Every direct phase-row table retains the entire original quadratic central sign. -/
theorem generatedSixth_monomial_mask_phase (k : Fin 4) :
    (generatedSixthMonomialSpinModel k).phase =
      representativeMatrix (generatedSixthMonomialMaskPhaseRows k) := by
  fin_cases k <;> rfl

/-- The direct translation, modulation and central labels describe the actual Q element. -/
theorem generatedSixth_monomial_mask_correction (k : Fin 4) :
    generatedSixthGeneratorCorrection (Fin.castAdd 1 k) =
      generatedAxisFourthQFromSpin
        (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
        (golayLabelCoefficients (generatedSixthMonomialMaskModulation k))
        (generatedSixthMonomialMaskCentral k) := by
  fin_cases k <;> rfl

/-- A direct bit-parity multiplication is encoded as a genuine twelve-bit source spin label. -/
def generatedSixthMonomialMaskLabel (rows : Fin 12 → Fin 4096) (n : ℕ) : Fin 4096 :=
  nortonUIntegerLabel (fun i =>
    if (monsterCo1GeometryBinaryMaskDot 12 (rows i).val n).testBit 0 then 1 else 0)

/-- Direct parity labels are precisely the original binary matrix-vector multiplication. -/
theorem generatedSixth_monomial_mask_label (rows : Fin 12 → Fin 4096) (n : ℕ) :
    golayLabelCoefficients (generatedSixthMonomialMaskLabel rows n) =
      representativeMatrix rows *ᵥ monsterCo1GeometryBinaryMaskDecode n := by
  rw [generatedSixthMonomialMaskLabel, nortonUIntegerLabel_inverse]
  exact (monsterCo1GeometryBinaryMaskMatrix_mulVec (fun i => (rows i).val) n).symm

/-- The direct original affine pullback uses XOR with the actual Q translation. -/
def generatedSixthMonomialFastPull (k : Fin 4) (n : Fin 4096) : Fin 4096 :=
  generatedSixthMonomialMaskLabel (generatedSixthMonomialMaskCoordinateRows k)
    (n.val ^^^ (generatedSixthMonomialMaskTranslation k).val)

/-- Both actual Q phases and the full original Parker quadratic sign use exact bit parity. -/
def generatedSixthMonomialFastPhase (k : Fin 4) (n : Fin 4096) : ZMod 2 :=
  generatedSixthMonomialMaskCentral k +
    (if (monsterCo1GeometryBinaryMaskDot 12
      (generatedSixthMonomialMaskModulation k).val n.val).testBit 0 then 1 else 0) +
    (if (generatedSixthMonomialMaskQuadratic
      (fun i => (generatedSixthMonomialMaskPhaseRows k i).val)
      (n.val ^^^ (generatedSixthMonomialMaskTranslation k).val)).testBit 0 then 1 else 0)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
