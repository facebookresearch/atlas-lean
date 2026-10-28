/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

/-! Candidate full Q images of the 24 positive coordinate lifts under the literal original spin
    word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Original translation, modulation and central coefficient candidates of 24 coordinate images. -/
def generatedNinthCoordinateImageLabels : Fin 24 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(273, 3352, 1), (655, 3721, 1), (3880, 1166, 0), (3912, 1055, 0), (3074, 1020, 0), (2054, 4091,
    1), (2676, 3414, 1), (917, 2728, 0), (227, 1540, 0), (1785, 3149, 0), (246, 2192, 0), (250,
    1169, 1), (2865, 1038, 1), (3023, 1039, 1), (2543, 1375, 1), (2673, 1710, 0), (1378, 740, 0),
    (2305, 3922, 0), (2824, 3995, 0), (3228, 253, 1), (2056, 3082, 0), (3986, 12, 1), (2920, 1168,
    0), (912, 1175, 1)]

/-- Complete candidate coordinate Q images, including the actual central coefficient. -/
def generatedNinthCoordinateImage (i : Fin 24) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedNinthCoordinateImageLabels i).1)
    (golayLabelCoefficients (generatedNinthCoordinateImageLabels i).2.1)),
    ofAdd (generatedNinthCoordinateImageLabels i).2.2⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
