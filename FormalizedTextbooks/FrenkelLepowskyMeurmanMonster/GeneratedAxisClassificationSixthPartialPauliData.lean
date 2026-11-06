/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPauliData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthAffinePauliModel

/-! Literal original Pauli products and projection matrices at all nine sixth-word stages. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Anchor labels for the original nine spin stages. -/
def generatedSixthPartialAnchor : Fin 9 → Fin 4096 := ![0, 0, 1024, 3, 336, 250, 96, 14, 0]

/-- Binary selectors for genuine products giving all affine support modulations. -/
def generatedSixthPartialPureSelector : Fin 9 → Fin 12 → Fin 4096 :=
  ![
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 0],
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 0],
  ![12, 22, 32, 70, 128, 1031, 2048, 0, 0, 0, 0, 0],
  ![12, 22, 32, 70, 128, 1031, 2048, 0, 0, 0, 0, 0],
  ![12, 22, 32, 70, 128, 1031, 2048, 0, 0, 0, 0, 0],
  ![12, 22, 32, 70, 128, 1031, 2048, 0, 0, 0, 0, 0],
  ![112, 170, 513, 1035, 2058, 0, 0, 0, 0, 0, 0, 0],
  ![112, 170, 513, 1035, 2058, 0, 0, 0, 0, 0, 0, 0],
  ![6, 48, 1035, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The original pure-modulation operators, retaining every preferred central bit. -/
def generatedSixthPartialPure (k : Fin 9) (j : Fin 12) : Q :=
  generatedSixthAffinePauliProduct (fun i => generatedSixthSpinPauliCache i k)
    (golayLabelCoefficients (generatedSixthPartialPureSelector k j))

/-- Literal rows of the translation projection, using twelve zero-padded parameters. -/
def generatedSixthPartialProjectionRows : Fin 9 → Fin 12 → Fin 4096 :=
  ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2048],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2048],
  ![3, 2048, 2049, 0, 0, 0, 0, 0, 12, 11, 0, 0],
  ![776, 3840, 2816, 0, 0, 0, 0, 0, 768, 512, 0, 0],
  ![512, 3232, 2208, 0, 0, 0, 0, 0, 160, 1664, 0, 0],
  ![1796, 2820, 3076, 0, 0, 0, 0, 0, 768, 1540, 0, 0],
  ![256, 2697, 2060, 5, 648, 9, 0, 0, 768, 0, 0, 0],
  ![320, 3200, 3072, 512, 1920, 1536, 0, 0, 864, 0, 0, 0],
  ![12, 3980, 0, 3340, 2058, 0, 526, 2442, 1664, 332, 0, 1670]]

/-- Literal complement columns for the actual pure-modulation equations. -/
def generatedSixthPartialComplementColumns : Fin 9 → Fin 12 → Fin 4096 :=
  ![
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 0],
  ![2045, 782, 268, 524, 816, 545, 960, 335, 12, 4, 2046, 0],
  ![512, 816, 544, 960, 320, 1008, 1024, 0, 0, 0, 0, 0],
  ![4, 21, 39, 133, 194, 150, 3, 0, 0, 0, 0, 0],
  ![346, 22, 74, 71, 82, 263, 336, 0, 0, 0, 0, 0],
  ![16, 218, 186, 219, 104, 129, 250, 0, 0, 0, 0, 0],
  ![66, 98, 2, 1042, 1120, 0, 0, 0, 0, 0, 0, 0],
  ![1, 2, 12, 20, 6, 0, 0, 0, 0, 0, 0, 0],
  ![32, 1, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The checked translation projection matrix at each original stage. -/
def generatedSixthPartialProjection (k : Fin 9) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayLabelCoefficients (generatedSixthPartialProjectionRows k i) j

/-- The checked complement matrix at each original stage. -/
def generatedSixthPartialComplement (k : Fin 9) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayLabelCoefficients (generatedSixthPartialComplementColumns k j) i

set_option maxHeartbeats 4000000 in
-- Verify 108 full products, including their original central phases.
/-- Every support operator is pure and its full central phase vanishes at the anchor. -/
theorem generatedSixth_partial_pure_certificate (k : Fin 9) :
    (∀ j, spinTranslation (generatedSixthPartialPure k j) = 0) ∧
    (∀ j, spinPhase (generatedSixthPartialPure k j)
      (golayLabelCoefficients (generatedSixthPartialAnchor k)) = 0) := by
  fin_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Verify nine 12-dimensional identities built from original Q coordinates.
/-- The actual translation projection and modulation complement add to identity. -/
theorem generatedSixth_partial_projection_certificate (k : Fin 9) :
    generatedSixthAffineTranslationMatrix (fun j => generatedSixthSpinPauliCache j k) *
      generatedSixthPartialProjection k +
      generatedSixthPartialComplement k *
        generatedSixthAffineModulationMatrix (generatedSixthPartialPure k) = 1 := by
  fin_cases k <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
