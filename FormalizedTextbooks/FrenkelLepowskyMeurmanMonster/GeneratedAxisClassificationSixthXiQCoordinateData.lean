/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiQImage

/-! Displayed full Q images of the 24 positive coordinates
require original-operator certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Original corrected Xi coordinate-image addresses and complete central phase candidates. -/
def generatedSixthXiCoordinateImageLabels : Fin 24 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![
    (2049, 58, 1), (809, 128, 0), (926, 2072, 0),
    (803, 250, 1), (3829, 2615, 1), (2816, 1002, 0),
    (2912, 881, 1), (2481, 302, 0), (3269, 3721, 1),
    (1253, 3994, 1), (1210, 3685, 1), (0, 1812, 0),
    (3150, 505, 0), (1893, 963, 0), (11, 852, 1),
    (1893, 969, 0), (2848, 377, 1), (538, 781, 1),
    (11, 784, 1), (2048, 128, 1), (2586, 557, 0),
    (2362, 68, 0), (11, 1872, 1), (913, 3144, 0)
  ]

/-- Full candidate Q images, before their original spin-conjugation equality is checked. -/
def generatedSixthXiCoordinateImage (i : Fin 24) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedSixthXiCoordinateImageLabels i).1)
      (golayLabelCoefficients (generatedSixthXiCoordinateImageLabels i).2.1)),
    ofAdd (generatedSixthXiCoordinateImageLabels i).2.2⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
