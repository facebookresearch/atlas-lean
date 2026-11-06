/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairQProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQWord

/-! Twelve original modulation images and the central frame translation, retaining every Q phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Literal coefficient labels for the twelve pure source modulation generators. -/
def generatedSixthPairQBasisLabels : Fin 12 → Fin 4096 :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

/-- Every complete original modulation-generator image, including its central sign. -/
def generatedSixthPairQBasisImages : Fin 12 → Q :=
  ![generatedAxisFourthQFromSpin (golayLabelCoefficients 2151)
      (golayLabelCoefficients 1753) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1473)
      (golayLabelCoefficients 2066) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1473)
      (golayLabelCoefficients 3570) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1599)
      (golayLabelCoefficients 1812) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2385)
      (golayLabelCoefficients 1154) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2385)
      (golayLabelCoefficients 2181) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 14)
      (golayLabelCoefficients 3942) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 686)
      (golayLabelCoefficients 349) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3117)
      (golayLabelCoefficients 3472) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 96)
      (golayLabelCoefficients 1009) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2969)
      (golayLabelCoefficients 2639) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 96)
      (golayLabelCoefficients 2416) 0]

/-- The literal source masks are exactly the ordinary twelve coordinate basis vectors. -/
theorem generatedSixth_pair_Q_basis_labels (j : Fin 12) :
    golayLabelCoefficients (generatedSixthPairQBasisLabels j) = Pi.single j 1 := by
  fin_cases j <;> funext i <;> fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Compute twelve full original eight-factor Q images, with both base and central coordinates.
/-- The bounded image table is checked against the genuine original word formula. -/
theorem generatedSixth_pair_Q_basis_certificate (j : Fin 12) :
    generatedSixthQImage (generatedAxisFourthQFromSpin 0
      (golayLabelCoefficients (generatedSixthPairQBasisLabels j)) 0) =
        generatedSixthPairQBasisImages j := by
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

/-- The genuine spin conjugation has precisely the checked modulation-basis images. -/
theorem generatedSixth_pair_Q_basis_image (j : Fin 12) :
    spinConjugation generatedSixthLocalFiber.val.1
        (generatedSixthPairModulationBasis j) = generatedSixthPairQBasisImages j := by
  unfold generatedSixthPairModulationBasis
  rw [← generatedSixth_pair_Q_basis_labels, generatedSixth_spin_conjugation,
    generatedSixth_pair_Q_basis_certificate]

/-- The actual complete image of the frame-class translation generator. -/
def generatedSixthPairQOmegaImage : Q :=
  generatedAxisFourthQFromSpin (golayLabelCoefficients 3058)
    (golayLabelCoefficients 2202) 0

set_option maxHeartbeats 2000000 in
-- Compute the original frame translation through the full eight-factor Q word.
/-- The frame translation image also retains the actual central phase. -/
theorem generatedSixth_pair_Q_omega_certificate :
    generatedSixthQImage
      (generatedAxisFourthQFromSpin (golayLabelCoefficients 2048) 0 0) =
        generatedSixthPairQOmegaImage := by
  apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

/-- The genuine spin conjugation realizes the checked full frame-translation image. -/
theorem generatedSixth_pair_Q_omega_image :
    spinConjugation generatedSixthLocalFiber.val.1
      (generatedAxisFourthQFromSpin (golayLabelCoefficients 2048) 0 0) =
        generatedSixthPairQOmegaImage := by
  rw [generatedSixth_spin_conjugation, generatedSixth_pair_Q_omega_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
