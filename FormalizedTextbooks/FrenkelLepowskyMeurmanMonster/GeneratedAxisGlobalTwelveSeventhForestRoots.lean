/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! The 35 roots of the Seventh singular forest. The zero mask and the eleven short-class
masks are excluded from the genuine binary Ω orbit, using actual norm-four Leech vectors; only
the last 23 roots can occur in the orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Masks of the eleven short-class forest roots. -/
def generatedAxisGlobalTwelveSeventhShortRootMask : Fin 11 → ℕ :=
  ![4249600, 4241408, 26624, 6293504, 61456, 485397, 2150480, 3190880, 5097554, 6948864, 6160384]

/-- Masks of the 23 type-four forest roots. -/
def generatedAxisGlobalTwelveSeventhLongRootMask : Fin 23 → ℕ :=
  ![2048, 1, 2051, 4, 17, 22, 129041, 3080450, 1446053, 4395183, 96, 97, 2242657, 272, 273, 274,
    6138124, 6169980, 4655104, 706833, 3737604, 2164742, 1900548]

/-- Physical integer representatives (scaled by `√8`) of the eleven short-class roots. -/
def generatedAxisGlobalTwelveSeventhShortRootPhysical : Fin 11 → Fin 24 → ℤ :=
  ![![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
   ![4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2],
   ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, -2, 2, 0, 0, 0, 0, 2, -2],
   ![0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2],
   ![0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2],
   ![0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2, 2, 0, -2, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveSeventhShortRootCoordinates : Fin 11 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![-6, 2, 1, 1, 1, 1, 1, -1, 1, 1, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0, -1, -1, 0, 2],
   ![20, -4, -3, -4, -4, -4, -5, 1, -3, -3, -4, 1, -4, 1, 2, 2, -4, 2, 1, 1, 1, 1, 2, -2],
   ![-8, 1, 1, 1, 2, 1, 2, 0, 1, 1, 2, 0, 2, -1, -1, -1, 1, 0, 0, -1, -1, 0, -1, 2],
   ![-8, 1, 1, 2, 1, 1, 2, 0, 1, 2, 1, 0, 1, 0, 0, -1, 2, -1, -1, -1, -1, -1, 0, 2],
   ![1, 0, -1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, -1, 0],
   ![2, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![-4, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check eleven complete lattice-coordinate, norm, and binary identities.
/-- Every short root has the stated basis coordinates, norm four, and binary class. -/
theorem generatedAxisGlobalTwelveSeventhShortRoot_certificate : ∀ k : Fin 11,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveSeventhShortRootCoordinates k =
      generatedAxisGlobalTwelveSeventhShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveSeventhShortRootPhysical k i) ^ 2) = 32 ∧
    leechHyperbolicInverse *ᵥ
        integerParity (generatedAxisGlobalTwelveSeventhShortRootCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSeventhShortRootMask k) := by
  decide +kernel

/-- The eleven genuine norm-four Leech vectors of the short roots. -/
def generatedAxisGlobalTwelveSeventhShortRootLattice (k : Fin 11) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalTwelveSeventhShortRootCoordinates k)

/-- Every short root mask lies outside the genuine binary Ω orbit. -/
theorem generatedAxisGlobalTwelveSeventhShortRoot_not_mem_orbit (k : Fin 11) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSeventhShortRootMask k) ∉
      generatedAxisGlobalBinaryOrbit := by
  have hp : (generatedAxisGlobalTwelveSeventhShortRootLattice k).val =
      generatedAxisGlobalTwelveSeventhShortRootPhysical k :=
    (generatedAxisGlobalTwelveSeventhShortRoot_certificate k).1
  have hn : leechSquareSum (generatedAxisGlobalTwelveSeventhShortRootLattice k).val = 32 := by
    rw [hp]
    exact (generatedAxisGlobalTwelveSeventhShortRoot_certificate k).2.1
  have hb : leechHyperbolicCoordinates
      (leechReduction (generatedAxisGlobalTwelveSeventhShortRootLattice k)) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSeventhShortRootMask k) := by
    rw [leechHyperbolicCoordinates_explicit]
    have hc : leechExplicitCoordinates (generatedAxisGlobalTwelveSeventhShortRootLattice k) =
        generatedAxisGlobalTwelveSeventhShortRootCoordinates k :=
      leechExplicitCoordinates.apply_symm_apply _
    rw [hc]
    exact (generatedAxisGlobalTwelveSeventhShortRoot_certificate k).2.2
  rw [← hb]
  exact generatedAxisGlobalBinary_short_excluded _ hn

/-- The 35 forest roots in order: zero, eleven short classes, 23 type-four classes. -/
def generatedAxisGlobalTwelveSeventhForestRootMask (k : Fin 35) : ℕ :=
  if h : k.val = 0 then 0
  else if h' : k.val < 12 then generatedAxisGlobalTwelveSeventhShortRootMask ⟨k.val - 1, by omega⟩
  else generatedAxisGlobalTwelveSeventhLongRootMask ⟨k.val - 12, by omega⟩

/-- The computational root list is the indexed root family. -/
theorem generatedAxisGlobalTwelveSeventhForestRootMasks_eq :
    seventhBitsetRoots = List.ofFn generatedAxisGlobalTwelveSeventhForestRootMask := by
  decide +kernel

/-- Membership in the root list is membership in the indexed root family. -/
theorem generatedAxisGlobalTwelveSeventhForestRootMasks_mem (b : ℕ) :
    b ∈ seventhBitsetRoots ↔
      ∃ k : Fin 35, generatedAxisGlobalTwelveSeventhForestRootMask k = b := by
  rw [generatedAxisGlobalTwelveSeventhForestRootMasks_eq, List.mem_ofFn]

/-- A forest root in the genuine binary Ω orbit is one of the last 23 roots. -/
theorem generatedAxisGlobalTwelveSeventhForestRoot_mem_orbit (k : Fin 35)
    (h : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSeventhForestRootMask k) ∈ generatedAxisGlobalBinaryOrbit) :
    12 ≤ k.val := by
  by_contra hk
  by_cases h0 : k.val = 0
  · simp only [generatedAxisGlobalTwelveSeventhForestRootMask, h0, ↓reduceDIte] at h
    have hz : monsterCo1GeometryBinaryMaskDecode (n := 24) 0 = 0 :=
      monsterCo1GeometryBinaryMaskDecode_zero
    rw [hz] at h
    exact generatedAxisGlobalBinary_ne_zero ⟨0, h⟩ rfl
  · have h' : k.val < 12 := by omega
    simp only [generatedAxisGlobalTwelveSeventhForestRootMask, h0, h', ↓reduceDIte] at h
    exact generatedAxisGlobalTwelveSeventhShortRoot_not_mem_orbit _ h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
