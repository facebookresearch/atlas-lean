/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
    FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightTransport

/-! Fifteen literal actual norm-eight lattice representatives of the selected frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The fifteen actual nonzero binary classes of the selected four-dimensional intersection. -/
def generatedFifthFrameIncidentMasks : Fin 15 → ℕ :=
  ![2048, 458752, 460800, 2686976, 2689024, 3014656, 3016704, 4194304, 4196352, 4653056,
      4655104, 6881280, 6883328, 7208960, 7211008]

/-- Binary coordinates of the fifteen displayed frame classes. -/
def generatedFifthFrameIncidentClass (j : Fin 15) : Fin 24 → ZMod 2 :=
  fun i => if (generatedFifthFrameIncidentMasks j).testBit i.val then 1 else 0

/-- Actual physical coordinates of fifteen norm-eight representatives inside the selected octad. -/
def generatedFifthFrameNormEightPhysical : Matrix (Fin 24) (Fin 15) ℤ :=
  ![
  ![-8, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4],
  ![0, -4, -4, 0, 0, 0, 0, -4, -4, -4, -4, 0, 0, 0, 0],
  ![0, 0, 0, -4, -4, 0, 0, -4, -4, 0, 0, -4, -4, 0, 0],
  ![0, 0, 0, 0, 0, -4, -4, -4, 4, 0, 0, 0, 0, -4, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -4, -4, -4, -4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, -4, 4, 0, 0, -4, -4, -4, -4, 0, 0],
  ![0, 0, 0, -4, 4, 0, 0, 0, 0, -4, 4, 0, 0, -4, -4],
  ![0, -4, 4, 0, 0, 0, 0, 0, 0, 0, 0, -4, 4, -4, 4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Exact integer lattice-basis coordinates of the same representatives. -/
def generatedFifthFrameNormEightInteger : Matrix (Fin 24) (Fin 15) ℤ :=
  ![
  ![-1, -3, 4, -2, 3, -3, 4, 1, 0, -6, -1, -7, 0, -6, 1],
  ![0, -1, -1, 0, 0, 1, -1, -1, -1, 0, 0, 1, 1, 0, 0],
  ![0, 1, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0, -2, 1, -1],
  ![0, 1, -1, 1, -1, 0, -2, -1, 1, 2, 0, 2, 0, 1, -1],
  ![0, 1, -1, 1, -1, 0, 0, 0, 0, 1, -1, 1, -1, 2, 0],
  ![0, 0, 0, 1, -1, 1, -1, 0, 0, 2, 0, 1, 1, 1, 1],
  ![0, 1, -1, 0, 0, 1, -1, 0, 0, 1, 1, 2, 0, 1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, -1, 1, -1, 0, 0, 2, 0, 1, 1, 1, 1],
  ![0, 1, -1, 0, 0, 1, -1, 0, 0, 1, 1, 2, 0, 1, -1],
  ![0, 1, -1, 1, -1, 0, 0, 0, 0, 1, -1, 1, -1, 2, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, -2, 0, -2, 0, -2, 0, 0, 2, 0, 2, 0, 2, 0],
  ![0, 0, 0, 0, 0, -2, 2, 0, 0, -2, -2, -2, -2, 0, 0],
  ![0, 0, 0, -2, 2, 0, 0, 0, 0, -2, 2, 0, 0, -2, -2],
  ![0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The displayed integer coordinates map to the displayed genuine physical vectors. -/
theorem generatedFifthFrame_norm_eight_physical_certificate : ∀ j : Fin 15,
    leechBasisMatrix *ᵥ generatedFifthFrameNormEightInteger.col j =
      generatedFifthFrameNormEightPhysical.col j := by
  decide +kernel

/-- Every displayed actual representative has squared physical norm eight. -/
theorem generatedFifthFrame_norm_eight_square_certificate : ∀ j : Fin 15,
    leechSquareSum (generatedFifthFrameNormEightPhysical.col j) = 64 := by
  decide +kernel

/-- Every displayed actual representative is supported inside the selected octad. -/
theorem generatedFifthFrame_norm_eight_support_certificate : ∀ j : Fin 15,
    generatedOctadSupported (golayOctadWord generatedFifthFlagOctad)
      (generatedFifthFrameNormEightPhysical.col j) := by
  simp only [generatedOctadSupported, golayOctadWord, generatedFifthFlagOctad_label]
  decide +kernel

/-- The displayed binary classes are the true hyperbolic reductions of the integer
    representatives. -/
theorem generatedFifthFrame_norm_eight_binary_certificate : ∀ j : Fin 15,
    leechHyperbolicInverse *ᵥ integerParity (generatedFifthFrameNormEightInteger.col j) =
      generatedFifthFrameIncidentClass j := by
  decide +kernel

/-- The fifteen displayed actual binary frame classes are pairwise distinct. -/
theorem generatedFifthFrameIncidentClass_injective :
    Function.Injective generatedFifthFrameIncidentClass := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
