/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineDirectionCoordinates

/-! Original spatial word and proposed basis certificates transporting the Ninth affine
marking directions to the original selected E8 section. Separate original matrix checks
bind every integral and binary coordinate before these data support a group bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A literal word in the two original Golay permutations moving octad2396 to octad2052. -/
def generatedNinthAffineOctadPermutation : golayAutomorphismSubgroup :=
  (omegaOrbitGolayPermutation 0)⁻¹ * (omegaOrbitGolayPermutation 0)⁻¹ *
    (omegaOrbitGolayPermutation 0)⁻¹ * omegaOrbitGolayPermutation 1 *
    omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 0 *
    omegaOrbitGolayPermutation 1 * omegaOrbitGolayPermutation 0 * omegaOrbitGolayPermutation 1

/-- Original forward physical coordinates of this Golay word. -/
def generatedNinthAffineOctadForward : Fin 24 → Fin 24 := ![0, 16, 20, 7, 17, 18, 10, 13, 3, 19,
      4, 23, 2, 1, 15, 11, 21, 14, 22, 9, 6, 8, 12, 5]

/-- Original inverse physical coordinates of the same word. -/
def generatedNinthAffineOctadInverse : Fin 24 → Fin 24 := ![0, 13, 12, 8, 10, 23, 20, 3, 21, 19,
      6, 15, 22, 7, 17, 14, 1, 4, 5, 9, 2, 16, 18, 11]

/-- The genuine complete lattice isometry transporting the original Ninth section. -/
def generatedNinthAffineTransport : leechIsomSubgroup :=
  golayPermutationIsometry generatedNinthAffineOctadPermutation * generatedNinthSectionTransport

/-- Proposed integral action matrix in the actual original Leech basis. -/
def generatedNinthAffineTransportBasisMatrix : Matrix (Fin 24) (Fin 24) ℤ := ![
    ![-3, -4, -1, -2, -2, -6, -5, 0, -1, -3, -14, -9, -3, -14, -9, -13, 1, -6, -8, -8, -1, -3,
      -19, -12],
    ![0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 3, 2, 1, 3, 2, 3, 0, 2, 2, 2, 1, 1, 5, 2],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 1, 0, 2, 1, 2, -1, 1, 1, 1, 0, 0, 3, 2],
    ![2, 2, 1, 1, 1, 1, 2, 0, 1, 1, 3, 2, 1, 3, 2, 2, 0, 1, 1, 1, 0, 1, 3, 3],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 3, 2, 0, 3, 2, 3, 0, 2, 2, 3, 0, 1, 4, 3],
    ![1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 3, 2, 1, 2, 2, 3, 0, 1, 1, 2, 0, 1, 3, 2],
    ![1, 1, 1, 0, 0, 2, 1, 0, 0, 1, 3, 2, 1, 3, 2, 3, 0, 1, 1, 1, 0, 1, 4, 3],
    ![0, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1, -1],
    ![1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 3, 2, 0, 2, 1, 2, 0, 1, 2, 2, 0, 0, 3, 2],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 2, 1, 0, 2, 1, 1, -1, 0, 1, 0, 0, -1, 3, 1],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 2, 2, 0, 3, 1, 2, -1, 1, 1, 1, 0, 1, 3, 2],
    ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0],
    ![-1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 3, 2, 3, -1, 2, 2, 2, 1, 0, 4, 2],
    ![2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, 1, -1, 1],
    ![0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, -1, 1, -1, 0, -1, 0, -1, -1, -1, 0, 0, -1, -1],
    ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, 1, 0, 0, 0, 0, 0, -1, -1],
    ![2, 1, 0, 1, 1, 2, 2, 0, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 1, 0, 1, 4, 3],
    ![-2, -1, -1, -1, -1, -1, -1, 0, -1, -1, -2, -1, -1, -1, -1, -1, -1, 0, -1, 0, 0, 0, -1, -1],
    ![-2, -1, -1, -1, -1, -1, -1, 0, -1, -1, -2, -1, -1, -1, -1, -1, -1, 0, -1, -1, 0, -1, -1, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1],
    ![0, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0, 0, -2, -1],
    ![0, 0, 0, 0, 0, -1, 0, 0, 0, 1, -1, 0, -1, -1, -1, -1, 0, 0, -1, 0, -1, 0, -2, -1],
    ![0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, -1, -1, -2, -1, -2, 0, -1, -1, -1, 0, -1, -2, -1],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 2, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 2, 1]]

/-- Proposed binary column labels after the actual integral-to-hyperbolic basis change. -/
def generatedNinthAffineTransportBinaryColumns : Fin 24 → ℕ := ![9071354, 9248091, 5611370,
      14637668, 674978, 16272207, 591876, 16083154, 3980133, 6327953, 2537366, 800768, 4201487,
      6204636, 5453820, 6687964, 7932115, 8124364, 698143, 1014723, 6753267, 4490255, 4646687,
      9737500]

/-- Original selected-section root labels of the eight actual discovered directions. -/
def generatedNinthAffineTransportRootLabels : Fin 8 → Fin 256 := ![114, 56, 121, 45, 199, 163,
      107, 246]

/-- Original genuine frame-system candidate reached by each transported whole direction space. -/
def generatedNinthAffineTransportSystemIndex : Fin 9 → Fin 270 := ![30, 150, 112, 147, 73, 16,
      180, 254, 205]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
