/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! The twenty roots of the Sixth singular forest. The zero mask and the nine short-class
masks are excluded from the genuine binary Ω orbit, using actual norm-four Leech vectors; only
the last ten roots can occur in the orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Masks of the nine short-class forest roots. -/
def generatedAxisGlobalTwelveSixthShortRootMask : Fin 9 → ℕ :=
  ![6293504, 4241408, 61456, 342048, 61472, 485397, 2603008, 6750208, 6160384]

/-- Masks of the ten type-four forest roots. -/
def generatedAxisGlobalTwelveSixthLongRootMask : Fin 10 → ℕ :=
  ![2048, 1, 4, 17, 272, 273, 6138124, 57361, 2557956, 1782870]

/-- Physical integer representatives (scaled by `√8`) of the nine short-class roots. -/
def generatedAxisGlobalTwelveSixthShortRootPhysical : Fin 9 → Fin 24 → ℤ :=
  ![![4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, 2, 0, -2],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
   ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, -2, 2, 0, 0, 0, 0, 2, -2],
   ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveSixthShortRootCoordinates : Fin 9 → Fin 24 → ℤ :=
  ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   ![-6, 2, 1, 1, 1, 1, 1, -1, 1, 1, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0, -1, -1, 0, 2],
   ![19, -4, -4, -4, -4, -3, -4, 1, -3, -4, -4, 2, -4, 2, 1, 2, -3, 0, 1, 2, 1, 2, 1, -2],
   ![-6, 1, 1, 1, 2, 1, 1, -1, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 2],
   ![20, -4, -3, -4, -4, -4, -5, 1, -3, -3, -4, 1, -4, 1, 2, 2, -4, 2, 1, 1, 1, 1, 2, -2],
   ![4, 0, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0],
   ![-4, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0],
   ![-4, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check nine complete lattice-coordinate, norm, and binary identities.
/-- Every short root has the stated basis coordinates, norm four, and binary class. -/
theorem generatedAxisGlobalTwelveSixthShortRoot_certificate : ∀ k : Fin 9,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveSixthShortRootCoordinates k =
      generatedAxisGlobalTwelveSixthShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveSixthShortRootPhysical k i) ^ 2) = 32 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalTwelveSixthShortRootCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSixthShortRootMask k) := by
  decide +kernel

/-- The nine genuine norm-four Leech vectors of the short roots. -/
def generatedAxisGlobalTwelveSixthShortRootLattice (k : Fin 9) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalTwelveSixthShortRootCoordinates k)

/-- Every short root mask lies outside the genuine binary Ω orbit. -/
theorem generatedAxisGlobalTwelveSixthShortRoot_not_mem_orbit (k : Fin 9) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSixthShortRootMask k) ∉
      generatedAxisGlobalBinaryOrbit := by
  have hp : (generatedAxisGlobalTwelveSixthShortRootLattice k).val =
      generatedAxisGlobalTwelveSixthShortRootPhysical k :=
    (generatedAxisGlobalTwelveSixthShortRoot_certificate k).1
  have hn : leechSquareSum (generatedAxisGlobalTwelveSixthShortRootLattice k).val = 32 := by
    rw [hp]
    exact (generatedAxisGlobalTwelveSixthShortRoot_certificate k).2.1
  have hb : leechHyperbolicCoordinates
      (leechReduction (generatedAxisGlobalTwelveSixthShortRootLattice k)) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSixthShortRootMask k) := by
    rw [leechHyperbolicCoordinates_explicit]
    have hc : leechExplicitCoordinates (generatedAxisGlobalTwelveSixthShortRootLattice k) =
        generatedAxisGlobalTwelveSixthShortRootCoordinates k :=
      leechExplicitCoordinates.apply_symm_apply _
    rw [hc]
    exact (generatedAxisGlobalTwelveSixthShortRoot_certificate k).2.2
  rw [← hb]
  exact generatedAxisGlobalBinary_short_excluded _ hn

/-- The twenty forest roots in order: zero, nine short classes, ten type-four classes. -/
def generatedAxisGlobalTwelveSixthForestRootMask (k : Fin 20) : ℕ :=
  if h : k.val = 0 then 0
  else if h' : k.val < 10 then generatedAxisGlobalTwelveSixthShortRootMask ⟨k.val - 1, by omega⟩
  else generatedAxisGlobalTwelveSixthLongRootMask ⟨k.val - 10, by omega⟩

/-- The computational root list is the indexed root family. -/
theorem generatedAxisGlobalTwelveSixthForestRootMasks_eq :
    sixthBitsetRoots = List.ofFn generatedAxisGlobalTwelveSixthForestRootMask := by
  decide +kernel

/-- Membership in the root list is membership in the indexed root family. -/
theorem generatedAxisGlobalTwelveSixthForestRootMasks_mem (b : ℕ) :
    b ∈ sixthBitsetRoots ↔
      ∃ k : Fin 20, generatedAxisGlobalTwelveSixthForestRootMask k = b := by
  rw [generatedAxisGlobalTwelveSixthForestRootMasks_eq, List.mem_ofFn]

/-- A forest root in the genuine binary Ω orbit is one of the last ten roots. -/
theorem generatedAxisGlobalTwelveSixthForestRoot_mem_orbit (k : Fin 20)
    (h : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSixthForestRootMask k) ∈ generatedAxisGlobalBinaryOrbit) :
    10 ≤ k.val := by
  by_contra hk
  by_cases h0 : k.val = 0
  · simp only [generatedAxisGlobalTwelveSixthForestRootMask, h0, ↓reduceDIte] at h
    have hz : monsterCo1GeometryBinaryMaskDecode (n := 24) 0 = 0 :=
      monsterCo1GeometryBinaryMaskDecode_zero
    rw [hz] at h
    exact generatedAxisGlobalBinary_ne_zero ⟨0, h⟩ rfl
  · have h' : k.val < 10 := by omega
    simp only [generatedAxisGlobalTwelveSixthForestRootMask, h0, h', ↓reduceDIte] at h
    exact generatedAxisGlobalTwelveSixthShortRoot_not_mem_orbit _ h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
