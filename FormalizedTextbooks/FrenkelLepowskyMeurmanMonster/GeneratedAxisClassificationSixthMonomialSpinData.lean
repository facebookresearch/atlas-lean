/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsTargetSpin

/-! Compact complete signed models of the four actual sixth monomial raw fibers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The three already certified original full source permutation targets. -/
def generatedSixthMonomialSpinTargets : Fin 3 → Fin 83 := ![0, 1, 3]

/-- Each actual first multiplication is recorded before conjugating by the inverse transporter. -/
def generatedSixthMonomialSpinPrefix : Fin 3 → RepresentativeSpinModel :=
  ![representativeSpinRowsModel
      ![1948, 8, 10, 1031, 16, 32, 402, 1743, 1509, 1653, 917, 3083]
      ![33, 48, 32, 32, 672, 1376, 0, 128, 256, 512, 1024, 0],
    representativeSpinRowsModel
      ![1065, 1706, 1160, 519, 1072, 32, 432, 864, 624, 480, 1024, 3083]
      ![545, 160, 1536, 1536, 32, 0, 512, 384, 256, 1024, 0, 0],
    representativeSpinRowsModel
      ![64, 1154, 161, 882, 519, 1370, 685, 439, 1509, 1653, 917, 3083]
      ![943, 94, 28, 1056, 1296, 224, 832, 640, 768, 512, 0, 0]]

/-- Full signed spin pullbacks of the first three conjugates and the fourth swap. -/
def generatedSixthMonomialSpinModel : Fin 4 → RepresentativeSpinModel :=
  ![representativeSpinRowsModel
      ![1031, 1037, 1035, 1038, 720, 864, 768, 256, 128, 192, 1024, 3087]
      ![0, 2, 4, 0, 0, 0, 256, 768, 0, 0, 1024, 0],
    representativeSpinRowsModel
      ![519, 1679, 523, 1435, 1021, 79, 1464, 1466, 536, 1999, 1973, 2733]
      ![1947, 204, 952, 72, 960, 800, 1920, 768, 512, 512, 1024, 0],
    representativeSpinRowsModel
      ![882, 979, 2038, 2035, 1088, 1940, 425, 1207, 62, 857, 1876, 3085]
      ![542, 606, 568, 1936, 1520, 960, 1408, 256, 1792, 512, 0, 0],
    representativeSpinRowsModel
      ![1706, 1699, 838, 1453, 46, 979, 889, 1566, 1152, 1216, 2004, 2971]
      ![1793, 482, 676, 1864, 1936, 608, 1344, 1280, 1536, 512, 1024, 0]]

/-- The source target model retains every actual preferred central quadratic coefficient. -/
def generatedSixthMonomialSpinSource (j : Fin 3) : RepresentativeSpinModel :=
  representativeSpinRowsModel
    (representativePermutationCoordinateRows (generatedSixthMonomialSpinTargets j))
    (representativePermutationPhaseRows (generatedSixthMonomialSpinTargets j))

/-- The recorded swap model is the complete checked original word profile. -/
theorem generatedSixth_monomial_spin_swap_model :
    generatedSixthMonomialSpinModel 3 = generatedSixthPermutationProfileModel 2 := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
