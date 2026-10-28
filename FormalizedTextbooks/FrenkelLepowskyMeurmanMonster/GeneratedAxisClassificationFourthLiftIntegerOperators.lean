/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftYPhaseFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftPPhaseFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftGammaPhaseFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagLiftGeometry

/-! Exact integer numerators of the genuine signed operators in the fourth flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original four Fourier terms, with integer signs and integer input. -/
def generatedFourthLiftIntY (f : SpinIndex → ℤ) (t : SpinIndex) : ℤ :=
  generatedFourthLiftIntSign (t 11) * generatedFourthLiftIntSign (generatedFourthLiftYPhaseFast t) *
    (generatedFourthLiftIntSign ((generatedFourthLiftYAddress t) 11) *
      f (generatedFourthLiftYAddress t) +
      f (monsterSpinOmegaFlip (generatedFourthLiftYAddress t))) +
    generatedFourthLiftIntSign (generatedFourthLiftYPhaseFast (monsterSpinOmegaFlip t)) *
    (generatedFourthLiftIntSign ((generatedFourthLiftYAddress (monsterSpinOmegaFlip t)) 11) *
      f (generatedFourthLiftYAddress (monsterSpinOmegaFlip t)) +
      f (monsterSpinOmegaFlip (generatedFourthLiftYAddress (monsterSpinOmegaFlip t))))

/-- The exact integer quadratic sign of the actual grey cocode Gaussian. -/
def generatedFourthLiftIntGamma (f : SpinIndex → ℤ) (t : SpinIndex) : ℤ :=
  -generatedFourthLiftIntSign (generatedFourthLiftGammaPhaseFast t) * f t

/-- The exact 64-translation integer numerator of the actual grey code Gaussian. -/
def generatedFourthLiftIntG (f : SpinIndex → ℤ) (t : SpinIndex) : ℤ :=
  ∑ a : XiGrayIndex, xiGraySign a * f (t + xiGrayCode a)

/-- The actual corrected Parker permutation, including its complete diagonal phase. -/
def generatedFourthLiftIntP (f : SpinIndex → ℤ) (t : SpinIndex) : ℤ :=
  generatedFourthLiftIntSign
    (generatedFourthLiftPPhaseFast (generatedFourthFlagLiftCode.symm t)) *
      f (generatedFourthFlagLiftCode.symm t)

/-- Twice the physical matrix of the actual normalized y82-corrected Xi lift. -/
def generatedFourthLiftSpatialNumerator (i j : Fin 24) : ℤ :=
  generatedFourthLiftIntSign (monsterSourceY82SignCode.val i) *
    co1XiNumerator (generatedFourthFlagCorrectionCoordinates i) j *
    generatedFourthLiftIntSign (monsterSourceY82SignCode.val j)

/-- The exact integer numerator of the normalized lift applied to the actual tensor. -/
def generatedFourthLiftTensorNumerator (t : SpinIndex) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, if generatedFourthLiftSpatialNumerator i j = 0 then 0 else
    generatedFourthLiftSpatialNumerator i j *
      generatedFourthLiftIntY (generatedFourthLiftIntP (generatedFourthLiftIntG
        (generatedFourthLiftIntGamma (generatedFourthLiftIntY
          (fun u => generatedFourthLiftIntegerTensor u j))))) t

/-- A concrete actual extraspecial correction, with its genuine additive central bit retained. -/
def generatedFourthFlagXiCorrection : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients 16) (golayLabelCoefficients 554)), ofAdd 1⟩

/-- The genuine local flag lift with this actual extraspecial correction. -/
noncomputable def generatedFourthFlagCorrectedLift : localFiberSubgroup :=
  localFiberIncl generatedFourthFlagXiCorrection * generatedFourthFlagNormalizedLift

/-- The full corrected tensor numerator, including the actual Pauli central phase. -/
def generatedFourthLiftCorrectedTensorNumerator (t : SpinIndex) (i : Fin 24) : ℤ :=
  generatedFourthLiftIntSign (spinPhase generatedFourthFlagXiCorrection t) *
    generatedFourthLiftTensorNumerator (t + spinTranslation generatedFourthFlagXiCorrection) i

/-- The literal four actual labels in the common affine plane. -/
def generatedFourthLiftPlaneLabels : Fin 4 → Fin 4096 := ![0, 14, 2048, 2062]

/-- Each actual nonzero tensor address is recorded by a genuine family label and plane label. -/
def generatedFourthLiftSupportAddress (k : Fin 28) (s : Fin 4) : SpinIndex :=
  generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k) +
    golayLabelCoefficients (generatedFourthLiftPlaneLabels s)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
