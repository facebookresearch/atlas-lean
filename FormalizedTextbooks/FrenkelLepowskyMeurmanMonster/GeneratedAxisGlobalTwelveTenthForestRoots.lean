/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! The 65 type-four forest roots are the actual binary roots of explicit words in the ten
original odd source letters, and the 22 remaining forest roots are excluded from the actual
binary Ω orbit: zero directly, and each short class by an explicit integral Leech vector of
norm four. Hence every point of the binary Ω orbit lies in the orbit of one of the 65 root words
under every subgroup of `Co1` containing the six gated Tenth letters. Word zero is empty: it is
the identity coset. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The masks of the 21 short-class roots. -/
def generatedAxisGlobalTwelveTenthShortRootMask : Fin 21 → ℕ :=
  ![
    3, 5, 6, 12, 13, 14, 16, 31, 65, 94, 110, 252, 394, 1008, 2830, 5106, 16384, 20480, 42495,
    3080395, 7784448]

/-- Physical integral representatives of norm four of the 21 short-class roots. -/
def generatedAxisGlobalTwelveTenthShortRootPhysical : Fin 21 → Fin 24 → ℤ :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2],
    ![0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 2, -2, 0, 0, 2, -2, 0, 0, 2, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2],
    ![0, 0, 0, 0, -2, -2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 2, 0, -2],
    ![0, 0, 0, 0, -2, -2, 0, 0, 2, 0, 2, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 2, -2],
    ![0, 0, 0, 0, 0, 2, -2, 0, 0, -2, 2, 0, 0, 0, 0, 0, -2, 0, -2, 0, 2, 2, 0, 0],
    ![0, 0, -2, 2, 0, -2, 0, 2, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 2, 0, 0, 2],
    ![0, -2, 2, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 2, 0, 2, 2, 0, 0],
    ![-2, 0, 0, -2, 0, 2, 2, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, -2, -2, 2, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2],
    ![0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -2, 2, 0, 2, 2, 0, 0, 0, 2, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveTenthShortRootCoordinates : Fin 21 → Fin 24 → ℤ :=
  ![
    ![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 0, 0],
    ![1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0],
    ![-18, 3, 3, 5, 4, 3, 3, -1, 4, 3, 3, -1, 2, -1, -1, -1, 4, -2, -2, -2, -2, 0, 0, 2],
    ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![14, -3, -2, -2, -4, -3, -3, 1, -3, -1, -2, 0, -3, 1, 2, 0, -3, 1, 2, 0, 1, 1, 2, -2],
    ![5, -2, -1, -1, -1, -1, -1, 0, -1, -1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 1, 1, 0, 0],
    ![-11, 2, 2, 2, 2, 2, 3, -1, 1, 2, 2, -1, 2, 0, -1, -1, 2, -1, 0, -1, 0, -1, -1, 2],
    ![16, -4, -3, -3, -3, -3, -4, 1, -2, -3, -2, 1, -3, 1, 1, 1, -3, 2, 0, 1, 1, 2, 1, -2],
    ![16, -3, -3, -3, -4, -3, -4, 1, -2, -2, -3, 1, -3, 0, 2, 1, -3, 1, 1, 1, 1, 1, 2, -2],
    ![2, -1, -1, 0, 0, 1, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 1, 1, 0, 0],
    ![-12, 2, 1, 3, 2, 2, 3, 0, 2, 3, 3, -1, 2, -1, -1, -2, 2, -1, -1, -1, 0, -1, -1, 2],
    ![0, -1, 1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![5, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0, 1, -1, 0, 1, 0, 1, 1, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    ![16, -3, -3, -4, -3, -3, -3, 1, -3, -3, -3, 2, -2, 0, 1, 1, -3, 2, 1, 1, 1, 1, 1, -2],
    ![16, -3, -3, -3, -3, -2, -4, 0, -3, -3, -3, 1, -3, 0, 2, 1, -3, 2, 1, 1, 1, 2, 1, -2],
    ![2, -1, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check 21 complete lattice-coordinate, norm, and binary identities.
/-- Every displayed short root has the exact basis coordinates, norm four, and binary class. -/
theorem generatedAxisGlobalTwelveTenthShortRoot_certificate : ∀ k : Fin 21,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveTenthShortRootCoordinates k =
      generatedAxisGlobalTwelveTenthShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveTenthShortRootPhysical k i) ^ 2) = 32 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalTwelveTenthShortRootCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTenthShortRootMask k) := by
  decide +kernel

/-- The integral Leech vectors of the short-class roots. -/
def generatedAxisGlobalTwelveTenthShortRootLattice (k : Fin 21) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalTwelveTenthShortRootCoordinates k)

/-- No short-class root lies in the actual binary Ω orbit. -/
theorem generatedAxisGlobalTwelveTenthShortRoot_not_mem_orbit (k : Fin 21) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTenthShortRootMask k) ∉
      generatedAxisGlobalBinaryOrbit := by
  have hc : leechExplicitCoordinates (generatedAxisGlobalTwelveTenthShortRootLattice k) =
      generatedAxisGlobalTwelveTenthShortRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  have hphys : (generatedAxisGlobalTwelveTenthShortRootLattice k).val =
      generatedAxisGlobalTwelveTenthShortRootPhysical k := by
    rw [← leechExplicitCoordinates_vector, hc]
    exact (generatedAxisGlobalTwelveTenthShortRoot_certificate k).1
  have hnorm : leechSquareSum (generatedAxisGlobalTwelveTenthShortRootLattice k).val = 32 := by
    rw [hphys]
    exact (generatedAxisGlobalTwelveTenthShortRoot_certificate k).2.1
  have hbin : leechHyperbolicCoordinates
      (leechReduction (generatedAxisGlobalTwelveTenthShortRootLattice k)) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTenthShortRootMask k) := by
    rw [leechHyperbolicCoordinates_explicit, hc]
    exact (generatedAxisGlobalTwelveTenthShortRoot_certificate k).2.2
  rw [← hbin]
  exact generatedAxisGlobalBinary_short_excluded _ hnorm

set_option maxRecDepth 100000 in
-- The 22 remaining forest roots are zero and the 21 short-class roots, in order.
theorem tenthForestOtherRoots_eq :
    tenthForestOtherRoots = 0 :: List.ofFn generatedAxisGlobalTwelveTenthShortRootMask := by
  decide +kernel

/-- None of the 22 remaining forest roots lies in the actual binary Ω orbit. -/
theorem tenthForestOtherRoots_not_mem_orbit (m : ℕ) (hm : m ∈ tenthForestOtherRoots) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) m ∉ generatedAxisGlobalBinaryOrbit := by
  rw [tenthForestOtherRoots_eq, List.mem_cons, List.mem_ofFn] at hm
  rcases hm with rfl | ⟨k, rfl⟩
  · intro h
    exact generatedAxisGlobalBinary_ne_zero ⟨_, h⟩ monsterCo1GeometryBinaryMaskDecode_zero
  · exact generatedAxisGlobalTwelveTenthShortRoot_not_mem_orbit k

/-- The masks of the 65 type-four roots. -/
def generatedAxisGlobalTwelveTenthRootMask : Fin 65 → ℕ :=
  ![
    2048, 4200704, 28680, 4694276, 4854020, 854030, 2152542, 3171222, 4612096, 5052430, 6297614,
    7365526, 4849756, 395270, 897028, 2099214, 4700174, 4218880, 7760640, 6414, 3345347, 4249856,
    4290816, 4614150, 4903004, 5312512, 7473920, 4653502, 6295552, 2797568, 3713792, 788540,
    4942606, 2153554, 897038, 4245564, 286720, 985102, 4130828, 4487936, 5183502, 4605963, 802816,
    838655, 897024, 2453504, 4245398, 4587520, 8372224, 4457224, 4194304, 4194316, 4245516,
    4593678, 5181440, 4243456, 5750796, 6339340, 5411070, 51212, 5722366, 6302718, 8093697,
    4179980, 983040]

set_option maxRecDepth 100000 in
-- The 65 type-four forest roots are the displayed masks, in order.
theorem tenthForestTypeFourRoots_eq :
    tenthForestTypeFourRoots = List.ofFn generatedAxisGlobalTwelveTenthRootMask := by
  decide +kernel

/-- Original odd source-letter words for the 65 type-four roots. -/
def generatedAxisGlobalTwelveTenthRootLetters : Fin 65 → List (Fin 10) :=
  ![
    [],
    [1, 9, 1, 6],
    [1, 9, 1, 7, 7],
    [1, 9, 1, 6, 6],
    [1, 9, 0, 6, 6],
    [1, 7, 0, 3],
    [1, 7, 1, 9, 6, 1],
    [1, 7, 1, 9, 7, 0],
    [1, 7, 9, 7],
    [1, 7, 1, 3],
    [1, 9, 6, 1],
    [1, 7, 0, 9, 7],
    [1, 7, 0, 9, 6, 1],
    [1, 7, 9, 7, 0],
    [1, 9, 6, 6, 1],
    [1, 9, 6, 0],
    [0, 9, 6, 1, 6],
    [1, 6, 9, 7],
    [1, 7, 9, 1, 7],
    [1, 9, 1, 6, 1],
    [1, 9, 1, 6, 1, 9],
    [1, 7, 9, 1, 6],
    [1, 9, 1, 5, 6],
    [1, 7, 9, 7, 1],
    [1, 7, 0, 9, 1, 6],
    [1, 7, 9, 7, 7],
    [1, 7, 9, 1, 7, 3],
    [1, 7, 0, 9, 1, 6, 6],
    [1, 9, 6],
    [1, 6, 9, 6, 6],
    [1, 9, 1, 5, 7],
    [1, 7, 0, 9, 6, 9],
    [1, 7, 7, 9, 0, 7],
    [1, 9, 1, 6, 9, 7, 7],
    [0, 9, 6, 0, 6],
    [1, 6, 0, 9, 0, 6, 9],
    [1, 6, 6, 9, 7],
    [1, 7, 0],
    [1, 7, 9, 0],
    [1, 9, 1, 7, 3],
    [1, 7, 1],
    [1, 7, 7, 7, 9, 6, 1],
    [1, 9, 6, 9, 7],
    [1, 7, 1, 3, 9, 1, 5],
    [1, 9, 6, 6],
    [1, 9, 7, 7, 7],
    [1, 7, 0, 9, 7, 9],
    [1, 7, 7],
    [1, 7, 9],
    [1, 9, 1, 7, 3, 0],
    [1],
    [0, 9, 0],
    [1, 9, 1],
    [1, 7, 1, 7],
    [1, 7],
    [1, 9],
    [1, 7, 9, 1, 3],
    [1, 9, 1, 7, 3, 0, 6, 5],
    [0, 9, 1, 7, 0, 3, 9],
    [0, 9, 1],
    [1, 9, 0, 7, 1, 5, 9],
    [1, 7, 0, 7, 9, 1, 5],
    [1, 7, 7, 9, 0, 7, 9, 5, 7, 1],
    [0, 7, 9, 1],
    [1, 7, 7, 0, 5, 6]]

/-- The explicit local transition word at each type-four root. -/
def generatedAxisGlobalTwelveTenthRootWord (k : Fin 65) : H :=
  ((generatedAxisGlobalTwelveTenthRootLetters k).map generatedAxisGlobalOddSourceLocalLetter).prod

private theorem tenthProduct_binary (ls : List (Fin 10)) (b : ℕ) :
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

set_option maxHeartbeats 4000000 in
-- Replay the 65 root words on their root masks.
/-- Every root word carries its root mask to the actual Ω mask. -/
theorem generatedAxisGlobalTwelveTenthRootLetters_certificate : ∀ k : Fin 65,
    (generatedAxisGlobalTwelveTenthRootLetters k).foldr (fun l x =>
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
        (generatedAxisGlobalTwelveTenthRootMask k) = 2048 := by
  decide +kernel

/-- The actual Ω coordinate is the mask 2048. -/
theorem generatedAxisGlobalTwelveTenth_omega_mask :
    toAdd (qQuotHom sourceOmegaQ) = monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 := by
  rw [sourceOmegaQ_eq_frame_class, leechFrame_zero_hyperbolic]
  funext i
  revert i
  decide +kernel

/-- The actual binary root of each root word is its root mask. -/
theorem generatedAxisGlobalTwelveTenthRootWord_root (k : Fin 65) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTenthRootWord k)).val =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTenthRootMask k) := by
  have hw : co1BinaryAction (projH (generatedAxisGlobalTwelveTenthRootWord k))
      (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTenthRootMask k)) =
      toAdd (qQuotHom sourceOmegaQ) := by
    rw [generatedAxisGlobalTwelveTenthRootWord, tenthProduct_binary,
      generatedAxisGlobalTwelveTenthRootLetters_certificate,
      generatedAxisGlobalTwelveTenth_omega_mask]
  change co1BinaryAction (projH (generatedAxisGlobalTwelveTenthRootWord k)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_inv, ← hw, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- The root word of the identity coset (root zero) is the identity. -/
theorem generatedAxisGlobalTwelveTenthRootWord_zero :
    generatedAxisGlobalTwelveTenthRootWord 0 = 1 := rfl

/-- Every point of the actual binary Ω orbit lies in the orbit of a type-four root mask, under
every subgroup of `Co1` containing the six gated Tenth letters. -/
theorem generatedAxisGlobalTwelveTenth_binary_cover (G : Subgroup Co1)
    (hG : ∀ g : Fin 6, generatedTenthAxisLowerRecoveryThreeProjectionLetter g ∈ G)
    (x : generatedAxisGlobalBinaryOrbit) :
    ∃ k : Fin 65, ∃ c ∈ G, co1BinaryAction c
      (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTenthRootMask k)) = x.val := by
  let b := (generatedAxisGlobalMaskFiniteEquiv 24).symm x.val
  have hb : monsterCo1GeometryBinaryMaskDecode (n := 24) b.val = x.val :=
    (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  have hlt : b.val < 16777216 := b.isLt
  have hs : generatedAxisGlobalMaskSingular b.val = true := by
    rw [generatedAxisGlobalMaskSingular_iff, hb]
    exact generatedAxisGlobalBinary_squareQuad x
  obtain ⟨m, hm, c, hc, he⟩ := tenthForest_reached G hG b.val hlt hs
  rw [hb] at he
  rcases List.mem_append.mp hm with h4 | ho
  · rw [tenthForestTypeFourRoots_eq, List.mem_ofFn] at h4
    obtain ⟨k, rfl⟩ := h4
    exact ⟨k, c, hc, he⟩
  · exfalso
    apply tenthForestOtherRoots_not_mem_orbit m ho
    obtain ⟨g, hg⟩ := x.property
    refine ⟨c⁻¹ * g, ?_⟩
    change co1BinaryAction (c⁻¹ * g) (toAdd (qQuotHom sourceOmegaQ)) = _
    rw [map_mul, LinearEquiv.mul_apply]
    change co1BinaryAction c⁻¹ (co1BinaryAction g (toAdd (qQuotHom sourceOmegaQ))) = _
    rw [show co1BinaryAction g (toAdd (qQuotHom sourceOmegaQ)) = x.val from hg, ← he, map_inv,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
