/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! The fifty-one roots of the Twelfth binary singular forest.

Thirty-eight roots lie in the actual binary Ω orbit; they are the targets of the Twelfth
transition words. Twelve roots are classes of genuine norm-four Leech vectors and the last root
is zero; these thirteen are excluded from the Ω orbit by actual lattice norms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The thirty-eight roots in the binary Ω orbit, as coordinate masks. -/
def generatedAxisGlobalTwelveTwelfthOmegaRootMask : Fin 38 → ℕ :=
  ![2048, 7389184, 990192, 3056, 3787772, 668566, 4196403, 4244464, 27632, 26878, 6295552,
    55308, 4587520, 1038348, 2885526, 4198400, 4243456, 2453504, 419734, 2910102, 592384, 6156,
    5202688, 4620734, 835478, 4249856, 51456, 1622462, 92416, 1495300, 2973696, 4809472,
    4290816, 5576610, 108892, 425984, 536576, 7385088]

/-- The twelve short-class roots, as coordinate masks. -/
def generatedAxisGlobalTwelveTwelfthShortRootMask : Fin 12 → ℕ :=
  ![4458496, 4257792, 1772150, 2754908, 7768064, 1112064, 4183822, 6574527, 6293504, 3153678,
    4720640, 5244928]

/-- Physical integer representatives of the twelve short-class roots. -/
def generatedAxisGlobalTwelveTwelfthShortRootPhysical : Fin 12 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, -4, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, 0, -2, 0, -2, -2, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -2],
    ![-2, -2, 0, 0, -2, -2, 0, 0, -2, -2, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0],
    ![0, 0, -4, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, -2, -2, 0, -2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 2, 0, 0],
    ![-2, -2, 0, 0, -2, 0, -2, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0],
    ![-4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, -2, -2, 0, -2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-4, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveTwelfthShortRootCoordinates : Fin 12 → Fin 24 → ℤ :=
  ![![1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![12, -2, -2, -2, -3, -3, -3, 1, -2, -2, -2, 0, -2, 1, 1, 1, -2, 1, 1, 1, 0, 1, 1, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, 1, 1, 0, -1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, -2, 0, 0],
    ![1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 1, 0, 0],
    ![4, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-3, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, -1, 1, 0, -1, 0, 0, -1, 0, 0],
    ![1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check twelve complete lattice-coordinate, norm, and binary identities.
/-- Every short-class root has the exact basis coordinates, norm four and stated binary class. -/
theorem generatedAxisGlobalTwelveTwelfthShortRoot_certificate : ∀ k : Fin 12,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveTwelfthShortRootCoordinates k =
      generatedAxisGlobalTwelveTwelfthShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveTwelfthShortRootPhysical k i)^2) = 32 ∧
    leechHyperbolicInverse *ᵥ
        integerParity (generatedAxisGlobalTwelveTwelfthShortRootCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTwelfthShortRootMask k) := by
  decide +kernel

/-- The twelve genuine integral Leech vectors. -/
def generatedAxisGlobalTwelveTwelfthShortRootLattice (k : Fin 12) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalTwelveTwelfthShortRootCoordinates k)

/-- Every short-class root is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalTwelveTwelfthShortRoot_not_mem_orbit (k : Fin 12) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveTwelfthShortRootMask k)
      ∉ generatedAxisGlobalBinaryOrbit := by
  have hc : leechExplicitCoordinates (generatedAxisGlobalTwelveTwelfthShortRootLattice k) =
      generatedAxisGlobalTwelveTwelfthShortRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  have hb : leechHyperbolicCoordinates
      (leechReduction (generatedAxisGlobalTwelveTwelfthShortRootLattice k)) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTwelfthShortRootMask k) := by
    rw [leechHyperbolicCoordinates_explicit, hc]
    exact (generatedAxisGlobalTwelveTwelfthShortRoot_certificate k).2.2
  have hn : leechSquareSum (generatedAxisGlobalTwelveTwelfthShortRootLattice k).val = 32 := by
    have hp : (generatedAxisGlobalTwelveTwelfthShortRootLattice k).val =
        generatedAxisGlobalTwelveTwelfthShortRootPhysical k :=
      (generatedAxisGlobalTwelveTwelfthShortRoot_certificate k).1
    rw [hp]
    exact (generatedAxisGlobalTwelveTwelfthShortRoot_certificate k).2.1
  rw [← hb]
  exact generatedAxisGlobalBinary_short_excluded _ hn

/-- The complete root list of the singular forest: Ω roots, short-class roots, zero. -/
def generatedAxisGlobalTwelveTwelfthForestRootMasks : List ℕ :=
  List.ofFn generatedAxisGlobalTwelveTwelfthOmegaRootMask ++
    List.ofFn generatedAxisGlobalTwelveTwelfthShortRootMask ++ [0]

/-- A forest root lying in the actual binary Ω orbit is one of the thirty-eight Ω roots. -/
theorem generatedAxisGlobalTwelveTwelfthForestRoot_omega (b : ℕ)
    (hb : b ∈ generatedAxisGlobalTwelveTwelfthForestRootMasks)
    (hx : monsterCo1GeometryBinaryMaskDecode (n := 24) b ∈ generatedAxisGlobalBinaryOrbit) :
    ∃ k : Fin 38, generatedAxisGlobalTwelveTwelfthOmegaRootMask k = b := by
  simp only [generatedAxisGlobalTwelveTwelfthForestRootMasks, List.mem_append, List.mem_ofFn,
    List.mem_singleton] at hb
  rcases hb with (hb | ⟨k, rfl⟩) | rfl
  · exact hb
  · exact absurd hx (generatedAxisGlobalTwelveTwelfthShortRoot_not_mem_orbit k)
  · exact (generatedAxisGlobalBinary_ne_zero ⟨_, hx⟩ monsterCo1GeometryBinaryMaskDecode_zero).elim

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
