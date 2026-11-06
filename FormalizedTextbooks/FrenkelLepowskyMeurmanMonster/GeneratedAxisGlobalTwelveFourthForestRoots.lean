/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! The twenty-seven roots of the Fourth-family singular binary forest: zero, ten
short-vector roots excluded from the actual binary Ω orbit by their genuine Leech norms, and
sixteen genuine Ω roots, each the actual binary root of an explicit original local source
word in Xi, the code signs four and five, and the two source permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Masks of the ten short-vector roots in the actual hyperbolic coordinate basis. -/
def generatedAxisGlobalTwelveFourthShortRootMask : Fin 10 → ℕ :=
  ![3, 6, 7, 14, 16, 48, 92, 4110, 14399, 4390912]

/-- The corresponding actual binary vectors. -/
def generatedAxisGlobalTwelveFourthShortRootBinary (k : Fin 10) (i : Fin 24) : ZMod 2 :=
  if (generatedAxisGlobalTwelveFourthShortRootMask k).testBit i.val then 1 else 0

/-- Concrete physical integer representatives of the ten short roots. -/
def generatedAxisGlobalTwelveFourthShortRootPhysical : Fin 10 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2],
    ![0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, -2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, -2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 2, -2, 0, 0, -2, 2, 0, 0, 0, 0, -2, 0, 0, -2, 2, 0, 2, 0],
    ![0, 0, 0, 0, -2, -2, -2, -2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2, -2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveFourthShortRootCoordinates : Fin 10 → Fin 24 → ℤ :=
  ![![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0],
    ![-14, 3, 3, 4, 4, 2, 2, -2, 3, 2, 2, -1, 2, -1, -1, -1, 2, -1, -1, -1, -2, 0, 0, 2],
    ![0, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-14, 3, 2, 2, 4, 3, 3, -1, 3, 1, 2, 0, 3, -1, -2, 0, 3, -1, -2, 0, -1, -1, -2, 2],
    ![0, 1, 0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, -1, 1, 0],
    ![2, -1, 0, 0, 0, 0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 0, -1, 0, 0, -1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-8, 2, 1, 1, 2, 2, 2, -1, 1, 1, 1, 0, 1, -1, -1, 0, 2, -1, -1, 0, 0, -1, -1, 2],
    ![-3, 1, 1, 1, 0, 0, 0, 0, 2, 1, 1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check ten complete lattice-coordinate, norm, and binary identities.
/-- Every displayed root has the exact basis coordinates, norm four, and stated binary class. -/
theorem generatedAxisGlobalTwelveFourthShortRoot_certificate : ∀ k : Fin 10,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveFourthShortRootCoordinates k =
      generatedAxisGlobalTwelveFourthShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveFourthShortRootPhysical k i)^2) = 32 ∧
    leechHyperbolicInverse *ᵥ
      integerParity (generatedAxisGlobalTwelveFourthShortRootCoordinates k) =
        generatedAxisGlobalTwelveFourthShortRootBinary k := by
  decide +kernel

/-- The ten genuine integral Leech vectors in the exact proved lattice model. -/
def generatedAxisGlobalTwelveFourthShortRootLattice (k : Fin 10) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalTwelveFourthShortRootCoordinates k)

/-- Their actual physical coordinates are exactly the finite checked representatives. -/
theorem generatedAxisGlobalTwelveFourthShortRootLattice_physical (k : Fin 10) :
    (generatedAxisGlobalTwelveFourthShortRootLattice k).val =
      generatedAxisGlobalTwelveFourthShortRootPhysical k :=
  (generatedAxisGlobalTwelveFourthShortRoot_certificate k).1

/-- Every short root has genuine Leech norm four. -/
theorem generatedAxisGlobalTwelveFourthShortRootLattice_norm (k : Fin 10) :
    leechSquareSum (generatedAxisGlobalTwelveFourthShortRootLattice k).val = 32 := by
  rw [generatedAxisGlobalTwelveFourthShortRootLattice_physical]
  exact (generatedAxisGlobalTwelveFourthShortRoot_certificate k).2.1

/-- The actual quotient coordinates are the displayed hyperbolic binary vectors. -/
theorem generatedAxisGlobalTwelveFourthShortRootLattice_binary (k : Fin 10) :
    leechHyperbolicCoordinates
      (leechReduction (generatedAxisGlobalTwelveFourthShortRootLattice k)) =
        generatedAxisGlobalTwelveFourthShortRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates (generatedAxisGlobalTwelveFourthShortRootLattice k) =
      generatedAxisGlobalTwelveFourthShortRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalTwelveFourthShortRoot_certificate k).2.2

/-- Every short root is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalTwelveFourthShortRoot_not_mem_orbit (k : Fin 10) :
    generatedAxisGlobalTwelveFourthShortRootBinary k ∉ generatedAxisGlobalBinaryOrbit := by
  rw [← generatedAxisGlobalTwelveFourthShortRootLattice_binary]
  exact generatedAxisGlobalBinary_short_excluded
    (generatedAxisGlobalTwelveFourthShortRootLattice k)
    (generatedAxisGlobalTwelveFourthShortRootLattice_norm k)

/-- Original source words in the ten signed letters for the sixteen genuine Ω roots. -/
def generatedAxisGlobalTwelveFourthRootWords : Fin 16 → List (Fin 10) :=
  ![[0, 6, 0, 8, 1],
    [0, 8],
    [0, 6, 0, 8],
    [0, 6, 8, 7, 0, 8],
    [0, 8, 6, 6, 0, 8],
    [0, 6, 0, 8, 0, 7, 8],
    [0, 6, 0, 8, 6, 8],
    [0, 6, 0, 8, 6],
    [0, 8, 6, 0, 8, 6],
    [0, 8, 6, 0, 8],
    [0, 8, 1, 6, 8],
    [],
    [1, 9, 6, 9, 7, 9, 7, 7, 7, 9, 6, 6, 9, 6, 9, 7, 7, 7, 3],
    [0, 6, 1, 8, 1],
    [0, 8, 0, 6, 8],
    [7, 7, 0, 6, 6, 6, 9, 7, 7, 7, 9, 7, 7, 9, 7, 9, 3]]

/-- Masks of the sixteen genuine Ω roots in the actual hyperbolic coordinate basis. -/
def generatedAxisGlobalTwelveFourthRootMask : Fin 16 → ℕ :=
  ![5229564, 4245504, 5227504, 5224440, 5983236, 7980904, 4255804, 6344796, 2285660, 5239792,
    788531, 2048, 528384, 8324080, 8187955, 2652160]

/-- The actual local source word of each root, with every original phase retained. -/
def generatedAxisGlobalTwelveFourthRootLocal (j : Fin 16) : H :=
  ((generatedAxisGlobalTwelveFourthRootWords j).map generatedAxisGlobalOddSourceLocalLetter).prod

private theorem fourthSourceProduct_binary (ls : List (Fin 10)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddSourceRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddSourceLocalLetter_binary]

set_option maxHeartbeats 20000000 in
-- Evaluate the sixteen original source words on their root masks.
/-- Every source word carries its root mask to the Ω mask. -/
theorem generatedAxisGlobalTwelveFourthRootWords_certificate : ∀ j : Fin 16,
    (generatedAxisGlobalTwelveFourthRootWords j).foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x)
        (generatedAxisGlobalTwelveFourthRootMask j) = 2048 := by
  decide +kernel

/-- The actual Ω class has hyperbolic mask 2048. -/
theorem generatedAxisGlobalTwelveFourth_omega_mask :
    monsterCo1GeometryBinaryMaskDecode 2048 = toAdd (qQuotHom sourceOmegaQ) := by
  decide +kernel

/-- Each explicit local word sends its genuine root mask to the actual Ω coordinate. -/
theorem generatedAxisGlobalTwelveFourthRootLocal_binary (j : Fin 16) :
    co1BinaryAction (projH (generatedAxisGlobalTwelveFourthRootLocal j))
      (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFourthRootMask j)) =
        toAdd (qQuotHom sourceOmegaQ) := by
  rw [generatedAxisGlobalTwelveFourthRootLocal, fourthSourceProduct_binary,
    generatedAxisGlobalTwelveFourthRootWords_certificate,
    generatedAxisGlobalTwelveFourth_omega_mask]

/-- The root-eleven word is empty. -/
theorem generatedAxisGlobalTwelveFourthRootLocal_eleven :
    generatedAxisGlobalTwelveFourthRootLocal 11 = 1 := rfl

/-- The sixteen genuine Ω roots, as actual binary roots of the explicit local words. -/
def generatedAxisGlobalTwelveFourthRoot (j : Fin 16) : generatedAxisGlobalBinaryOrbit :=
  generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveFourthRootLocal j)

/-- The actual binary root of each local word has exactly the displayed root mask. -/
theorem generatedAxisGlobalTwelveFourthRoot_val (j : Fin 16) :
    (generatedAxisGlobalTwelveFourthRoot j).val =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFourthRootMask j) := by
  change co1BinaryAction (projH (generatedAxisGlobalTwelveFourthRootLocal j)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_inv, ← generatedAxisGlobalTwelveFourthRootLocal_binary j, ← LinearEquiv.mul_apply,
    ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- The singular forest has zero, ten short roots, and sixteen genuine Ω roots. -/
def generatedAxisGlobalTwelveFourthForestRootMask (k : Fin 27) : ℕ :=
  if h : k.val = 0 then 0
  else if h' : k.val < 11 then generatedAxisGlobalTwelveFourthShortRootMask ⟨k.val - 1, by omega⟩
  else generatedAxisGlobalTwelveFourthRootMask ⟨k.val - 11, by omega⟩

set_option maxHeartbeats 1000000 in
-- Check the exact bounded root list in the actual coordinate-mask encoding.
/-- Every singular forest root is a bounded genuine 24-coordinate mask. -/
theorem generatedAxisGlobalTwelveFourthForestRootMask_lt (k : Fin 27) :
    generatedAxisGlobalTwelveFourthForestRootMask k < 2 ^ 24 := by
  revert k
  decide +kernel

/-- A genuine Ω orbit point with a forest-root mask is one of the sixteen Ω roots. -/
theorem generatedAxisGlobalTwelveFourthForestRoot_cases (k : Fin 27)
    (x : generatedAxisGlobalBinaryOrbit)
    (hx : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveFourthForestRootMask k) = x.val) :
    ∃ j : Fin 16, x = generatedAxisGlobalTwelveFourthRoot j := by
  by_cases h : k.val = 0
  · simp only [generatedAxisGlobalTwelveFourthForestRootMask, h, ↓reduceDIte,
      monsterCo1GeometryBinaryMaskDecode_zero] at hx
    exact absurd hx.symm (generatedAxisGlobalBinary_ne_zero x)
  · by_cases h' : k.val < 11
    · simp only [generatedAxisGlobalTwelveFourthForestRootMask, h, h', ↓reduceDIte] at hx
      have hn := generatedAxisGlobalTwelveFourthShortRoot_not_mem_orbit
        (⟨k.val - 1, by omega⟩ : Fin 10)
      change monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalTwelveFourthShortRootMask ⟨k.val - 1, by omega⟩) ∉
          generatedAxisGlobalBinaryOrbit at hn
      rw [hx] at hn
      exact absurd x.property hn
    · simp only [generatedAxisGlobalTwelveFourthForestRootMask, h, h', ↓reduceDIte] at hx
      refine ⟨⟨k.val - 11, by omega⟩, Subtype.ext ?_⟩
      rw [generatedAxisGlobalTwelveFourthRoot_val, hx]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
