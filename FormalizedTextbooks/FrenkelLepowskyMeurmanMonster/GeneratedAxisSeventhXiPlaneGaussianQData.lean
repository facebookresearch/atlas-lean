/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlanePauliGaussian
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseLabels

/-! Literal coordinates retaining all sixty-four genuine corrected Pauli phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Translation, modulation, and central coefficient of each actual Gaussian Q element. -/
def generatedSeventhXiPlaneGaussianQData : Fin 64 → Fin 3 → ℕ :=
  ![
    ![1804, 1613, 1],
    ![2895, 227, 0],
    ![2005, 735, 1],
    ![2966, 1137, 0],
    ![3645, 55, 0],
    ![638, 1689, 0],
    ![3812, 1189, 1],
    ![679, 523, 1],
    ![3139, 471, 0],
    ![0, 1913, 1],
    ![3226, 1349, 1],
    ![217, 1003, 0],
    ![1394, 1965, 1],
    ![2353, 259, 1],
    ![1451, 831, 1],
    ![2536, 1425, 1],
    ![2889, 467, 1],
    ![1802, 1917, 0],
    ![2960, 1345, 0],
    ![2003, 1007, 1],
    ![632, 1961, 0],
    ![3643, 263, 0],
    ![673, 827, 0],
    ![3810, 1429, 0],
    ![6, 1609, 1],
    ![3141, 231, 0],
    ![223, 731, 1],
    ![3228, 1141, 0],
    ![2359, 51, 0],
    ![1396, 1693, 0],
    ![2542, 1185, 1],
    ![1453, 527, 1],
    ![3501, 527, 1],
    ![494, 1185, 1],
    ![3444, 1693, 0],
    ![311, 51, 0],
    ![1180, 1141, 0],
    ![2271, 731, 1],
    ![1093, 231, 0],
    ![2054, 1609, 1],
    ![1762, 1429, 0],
    ![2721, 827, 0],
    ![1595, 263, 0],
    ![2680, 1961, 0],
    ![4051, 1007, 1],
    ![912, 1345, 0],
    ![3850, 1917, 0],
    ![841, 467, 1],
    ![488, 1425, 1],
    ![3499, 831, 1],
    ![305, 259, 1],
    ![3442, 1965, 1],
    ![2265, 1003, 0],
    ![1178, 1349, 1],
    ![2048, 1913, 1],
    ![1091, 471, 0],
    ![2727, 523, 1],
    ![1764, 1189, 1],
    ![2686, 1689, 0],
    ![1597, 55, 0],
    ![918, 1137, 0],
    ![4053, 735, 1],
    ![847, 227, 0],
    ![3852, 1613, 1]
  ]

/-- Full extraspecial elements reconstructed from the literal twelve-bit coordinates. -/
def generatedSeventhXiPlaneGaussianQLiteral (a : Fin 64) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients ⟨generatedSeventhXiPlaneGaussianQData a 0 % 4096,
      Nat.mod_lt _ (by decide)⟩)
    (golayLabelCoefficients ⟨generatedSeventhXiPlaneGaussianQData a 1 % 4096,
      Nat.mod_lt _ (by decide)⟩)),
    ofAdd (generatedSeventhXiPlaneGaussianQData a 2 : ZMod 2)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
