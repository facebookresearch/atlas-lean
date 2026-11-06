/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlanePauliBitPhases

/-! Exact small data for the full original sixty-four-term integer spin evaluator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The literal translation label of each source-verified Gaussian Q element. -/
def generatedSeventhXiPlaneGaussianTranslationLabel (a : Fin 64) : Fin 4096 :=
  ⟨generatedSeventhXiPlaneGaussianQData a 0 % 4096, Nat.mod_lt _ (by decide)⟩

/-- Its actual source modulation label. -/
def generatedSeventhXiPlaneGaussianModulationLabel (a : Fin 64) : Fin 4096 :=
  ⟨generatedSeventhXiPlaneGaussianQData a 1 % 4096, Nat.mod_lt _ (by decide)⟩

/-- The original literal central sign, retained independently of both binary labels. -/
def generatedSeventhXiPlaneGaussianCentralSign (a : Fin 64) : ℤ :=
  if generatedSeventhXiPlaneGaussianQData a 2 = 0 then 1 else -1

/-- All sixty-four published grey quadratic signs as exact individual bits. -/
def generatedSeventhXiPlaneGaussianGraySign (a : Fin 64) : ℤ :=
  if (0x8117177e177e7ee8 : ℕ).testBit a.val then -1 else 1

/-- The complete genuine Pauli phase evaluated by its source modulation and central bit. -/
def generatedSeventhXiPlaneGaussianBitPhase (a : Fin 64) (d : Fin 4096) : ℤ :=
  generatedSeventhXiPlaneGaussianCentralSign a *
    (if monsterNortonBitParity
      ((generatedSeventhXiPlaneGaussianModulationLabel a).val &&& d.val) then -1 else 1)

/-- The literal translation is the actual full extraspecial translation. -/
theorem generatedSeventhXiPlaneGaussian_translation (a : Fin 64) :
    spinTranslation (generatedSeventhXiPlaneGaussianQLiteral a) =
      golayLabelCoefficients (generatedSeventhXiPlaneGaussianTranslationLabel a) := by
  funext i
  exact Fin.append_left _ _ _

/-- The literal modulation is the actual full extraspecial modulation. -/
theorem generatedSeventhXiPlaneGaussian_modulation (a : Fin 64) :
    spinModulation (generatedSeventhXiPlaneGaussianQLiteral a) =
      golayLabelCoefficients (generatedSeventhXiPlaneGaussianModulationLabel a) := by
  funext i
  exact Fin.append_right _ _ _

set_option maxRecDepth 10000 in
/-- Every original central sign is verified against the actual source-checked Q coefficient. -/
theorem generatedSeventhXiPlaneGaussian_central_sign : ∀ a : Fin 64,
    nortonUIntegerSign (toAdd (generatedSeventhXiPlaneGaussianQLiteral a).coeff) =
      generatedSeventhXiPlaneGaussianCentralSign a := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- Every compact grey sign retains the original actual nonsingular quadratic phase. -/
theorem generatedSeventhXiPlaneGaussian_gray_sign : ∀ a : Fin 64,
    xiGraySign (monsterNortonGrayCoefficients a) = generatedSeventhXiPlaneGaussianGraySign a := by
  decide +kernel

/-- The fast Pauli phase equals the original source phase on every actual spin coordinate. -/
theorem generatedSeventhXiPlaneGaussian_bit_phase (a : Fin 64) (d : Fin 4096) :
    nortonUIntegerSign (spinPhase (generatedSeventhXiPlaneGaussianQLiteral a)
      (golayLabelCoefficients d)) = generatedSeventhXiPlaneGaussianBitPhase a d := by
  rw [spinPhase, generatedSeventhXi_integer_sign_add,
    generatedSeventhXiPlaneGaussian_modulation, generatedSeventhXi_integer_dot_phase,
    generatedSeventhXiPlaneGaussian_central_sign]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
