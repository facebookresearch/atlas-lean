/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightForestCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! The 23 type-four root-eight forest roots are the actual binary roots of explicit words in the
ten original odd source letters, and the 13 remaining forest roots are excluded from the actual
binary Ω orbit: zero directly, and each short class by an explicit integral Leech vector of norm
four. Hence every point of the binary Ω orbit lies in the orbit of one of the 23 root words under
every subgroup of `Co1` containing lifts of the four root-eight letters. Word zero is empty: it
is the identity coset. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The masks of the 12 short-class roots. -/
def rootEightForestShortMask : Fin 12 → ℕ :=
  ![
    3, 6, 7, 31, 32, 64, 92, 193, 5902, 17674, 327692, 6162432]

/-- Physical integral representatives of norm four of the 12 short-class roots. -/
def rootEightForestShortPhysical : Fin 12 → Fin 24 → ℤ :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, -2],
    ![0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0],
    ![0, 0, 0, 0, 0, 0, 2, -2, 0, 0, -2, 2, 0, 0, 0, 0, -2, 0, 0, -2, 2, 0, 2, 0],
    ![0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 0],
    ![2, -2, -2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0],
    ![0, -2, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 2, 2, 2, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, -2, 2, 2, 2, -2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def rootEightForestShortCoordinates : Fin 12 → Fin 24 → ℤ :=
  ![
    ![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0],
    ![-14, 3, 3, 4, 4, 2, 2, -2, 3, 2, 2, -1, 2, -1, -1, -1, 2, -1, -1, -1, -2, 0, 0, 2],
    ![5, -2, -1, -1, -1, -1, -1, 0, -1, -1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 1, 1, 0, 0],
    ![14, -4, -2, -2, -3, -3, -3, 1, -3, -2, -1, 0, -3, 2, 1, 0, -3, 2, 1, 0, 1, 2, 1, -2],
    ![-2, 1, -1, 1, 0, 2, 1, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, 1, 0, 1, -1, 0],
    ![2, -1, 0, 0, 0, 0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 0, -1, 0, 0, -1, 1, 0, 1, 0],
    ![7, -2, -1, -2, -1, -2, -2, 1, -1, -1, -1, 0, -1, 0, 0, 1, -1, 1, 0, 0, 1, 0, 1, 0],
    ![4, -1, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0, 1, -1, 0, 1, 0, 0, 1, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 1, 0, 0, 0, -1, 0],
    ![18, -5, -3, -3, -3, -3, -4, 1, -3, -3, -2, 1, -4, 1, 1, 1, -4, 2, 0, 0, 2, 2, 2, -2],
    ![3, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check 12 complete lattice-coordinate, norm, and binary identities.
/-- Every displayed short root has the exact basis coordinates, norm four, and binary class. -/
theorem rootEightForestShort_certificate : ∀ k : Fin 12,
    leechBasisMatrix *ᵥ rootEightForestShortCoordinates k = rootEightForestShortPhysical k ∧
    (∑ i : Fin 24, (rootEightForestShortPhysical k i) ^ 2) = 32 ∧
    leechHyperbolicInverse *ᵥ integerParity (rootEightForestShortCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (rootEightForestShortMask k) := by
  decide +kernel

/-- The integral Leech vectors of the short-class roots. -/
def rootEightForestShortLattice (k : Fin 12) : leechIntegral :=
  leechExplicitCoordinateMap (rootEightForestShortCoordinates k)

/-- No short-class root lies in the actual binary Ω orbit. -/
theorem rootEightForestShort_not_mem_orbit (k : Fin 12) :
    monsterCo1GeometryBinaryMaskDecode (rootEightForestShortMask k) ∉
      generatedAxisGlobalBinaryOrbit := by
  have hc : leechExplicitCoordinates (rootEightForestShortLattice k) =
      rootEightForestShortCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  have hphys : (rootEightForestShortLattice k).val = rootEightForestShortPhysical k := by
    rw [← leechExplicitCoordinates_vector, hc]
    exact (rootEightForestShort_certificate k).1
  have hnorm : leechSquareSum (rootEightForestShortLattice k).val = 32 := by
    rw [hphys]
    exact (rootEightForestShort_certificate k).2.1
  have hbin : leechHyperbolicCoordinates (leechReduction (rootEightForestShortLattice k)) =
      monsterCo1GeometryBinaryMaskDecode (rootEightForestShortMask k) := by
    rw [leechHyperbolicCoordinates_explicit, hc]
    exact (rootEightForestShort_certificate k).2.2
  rw [← hbin]
  exact generatedAxisGlobalBinary_short_excluded _ hnorm

set_option maxRecDepth 100000 in
-- The 13 remaining forest roots are zero and the 12 short-class roots, in order.
theorem rootEightForestOtherRoots_eq :
    rootEightForestOtherRoots = 0 :: List.ofFn rootEightForestShortMask := by
  decide +kernel

/-- None of the 13 remaining forest roots lies in the actual binary Ω orbit. -/
theorem rootEightForestOtherRoots_not_mem_orbit (m : ℕ) (hm : m ∈ rootEightForestOtherRoots) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) m ∉ generatedAxisGlobalBinaryOrbit := by
  rw [rootEightForestOtherRoots_eq, List.mem_cons, List.mem_ofFn] at hm
  rcases hm with rfl | ⟨k, rfl⟩
  · intro h
    exact generatedAxisGlobalBinary_ne_zero ⟨_, h⟩ monsterCo1GeometryBinaryMaskDecode_zero
  · exact rootEightForestShort_not_mem_orbit k

/-- The masks of the 23 type-four roots. -/
def rootEightForestRootMask : Fin 23 → ℕ :=
  ![
    2048, 2304, 985102, 5181440, 3148544, 4201216, 5183502, 919566, 4200704, 6295808, 28680,
    854030, 4130828, 3147790, 4245504, 4243456, 4194574, 4612096, 4917248, 4766464, 4196352,
    1574924, 7340036]

set_option maxRecDepth 100000 in
-- The 23 type-four forest roots are the displayed masks, in order.
theorem rootEightForestTypeFourRoots_eq :
    rootEightForestTypeFourRoots = List.ofFn rootEightForestRootMask := by
  decide +kernel

/-- Original odd source-letter words for the 23 type-four roots. -/
def rootEightForestRootLetters : Fin 23 → List (Fin 10) :=
  ![
    [],
    [0, 9, 1, 6],
    [1, 7, 0],
    [1, 7],
    [1, 9, 0, 7],
    [1, 9, 1, 7],
    [1, 7, 1],
    [1, 7, 0, 5],
    [1, 9, 1, 6],
    [0, 9, 0, 6],
    [1, 9, 1, 7, 7],
    [1, 7, 0, 3],
    [1, 7, 9, 0],
    [1, 9, 7, 0],
    [0, 9],
    [1, 9],
    [1, 9, 1, 6, 0],
    [1, 7, 9, 7],
    [1, 7, 7, 0, 7],
    [1, 9, 1, 7, 5],
    [0],
    [1, 6, 9, 0, 3],
    [0, 6, 9, 7, 9, 0]]

/-- The explicit local transition word at each type-four root. -/
def rootEightForestRootWord (k : Fin 23) : H :=
  ((rootEightForestRootLetters k).map generatedAxisGlobalOddSourceLocalLetter).prod

private theorem rootEightProduct_binary (ls : List (Fin 10)) (b : ℕ) :
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
-- Replay the 23 root words on their root masks.
/-- Every root word carries its root mask to the actual Ω mask. -/
theorem rootEightForestRootLetters_certificate : ∀ k : Fin 23,
    (rootEightForestRootLetters k).foldr (fun l x =>
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
        (rootEightForestRootMask k) = 2048 := by
  decide +kernel

/-- The actual Ω coordinate is the mask 2048. -/
theorem rootEightForest_omega_mask :
    toAdd (qQuotHom sourceOmegaQ) = monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 := by
  rw [sourceOmegaQ_eq_frame_class, leechFrame_zero_hyperbolic]
  funext i
  revert i
  decide +kernel

/-- The actual binary root of each root word is its root mask. -/
theorem rootEightForestRootWord_root (k : Fin 23) :
    (generatedAxisGlobalBinaryRoot (rootEightForestRootWord k)).val =
      monsterCo1GeometryBinaryMaskDecode (rootEightForestRootMask k) := by
  have hw : co1BinaryAction (projH (rootEightForestRootWord k))
      (monsterCo1GeometryBinaryMaskDecode (rootEightForestRootMask k)) =
      toAdd (qQuotHom sourceOmegaQ) := by
    rw [rootEightForestRootWord, rootEightProduct_binary, rootEightForestRootLetters_certificate,
      rootEightForest_omega_mask]
  change co1BinaryAction (projH (rootEightForestRootWord k)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_inv, ← hw, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- The root word of the identity coset (root zero) is the identity. -/
theorem rootEightForestRootWord_zero : rootEightForestRootWord 0 = 1 := rfl

/-- Every point of the actual binary Ω orbit lies in the orbit of a type-four root mask, under
every subgroup of `Co1` containing lifts of the four root-eight letters. -/
theorem rootEightForest_binary_cover {L : Fin 4 → Co1} (hL : RootEightForestLifts L)
    (G : Subgroup Co1) (hG : ∀ g : Fin 4, L g ∈ G) (x : generatedAxisGlobalBinaryOrbit) :
    ∃ k : Fin 23, ∃ c ∈ G, co1BinaryAction c
      (monsterCo1GeometryBinaryMaskDecode (rootEightForestRootMask k)) = x.val := by
  let b := (generatedAxisGlobalMaskFiniteEquiv 24).symm x.val
  have hb : monsterCo1GeometryBinaryMaskDecode (n := 24) b.val = x.val :=
    (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  have hlt : b.val < 16777216 := b.isLt
  have hs : generatedAxisGlobalMaskSingular b.val = true := by
    rw [generatedAxisGlobalMaskSingular_iff, hb]
    exact generatedAxisGlobalBinary_squareQuad x
  obtain ⟨m, hm, c, hc, he⟩ := rootEightForest_reached hL G hG b.val hlt hs
  rw [hb] at he
  rcases List.mem_append.mp hm with h4 | ho
  · rw [rootEightForestTypeFourRoots_eq, List.mem_ofFn] at h4
    obtain ⟨k, rfl⟩ := h4
    exact ⟨k, c, hc, he⟩
  · exfalso
    apply rootEightForestOtherRoots_not_mem_orbit m ho
    obtain ⟨g, hg⟩ := x.property
    refine ⟨c⁻¹ * g, ?_⟩
    change co1BinaryAction (c⁻¹ * g) (toAdd (qQuotHom sourceOmegaQ)) = _
    rw [map_mul, LinearEquiv.mul_apply]
    change co1BinaryAction c⁻¹ (co1BinaryAction g (toAdd (qQuotHom sourceOmegaQ))) = _
    rw [show co1BinaryAction g (toAdd (qQuotHom sourceOmegaQ)) = x.val from hg, ← he, map_inv,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
