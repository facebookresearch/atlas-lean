/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8OrthogonalShortReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskColumns

/-! Three explicit Golay-automorphism involutions preserving the physical octad-three block
`{8, ..., 15}`, with their exact integral lattice actions and binary column masks.
The arrays were found numerically; every stated property is checked by Lean's kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Forward coordinate arrays of the three involutions. -/
def generatedAxisGlobalTwelveOctadPermForward : Fin 3 → Fin 24 → Fin 24 :=
  ![![16, 3, 18, 1, 22, 5, 20, 7, 8, 15, 14, 11, 12, 13, 10, 9, 0, 19, 2, 17, 6, 21, 4, 23],
    ![20, 21, 5, 4, 3, 2, 18, 19, 13, 11, 14, 9, 15, 8, 10, 12, 23, 22, 6, 7, 0, 1, 17, 16],
    ![5, 18, 17, 6, 23, 0, 3, 20, 10, 13, 8, 12, 11, 9, 15, 14, 21, 2, 1, 22, 7, 16, 19, 4]]

set_option maxHeartbeats 2000000 in
-- Check the involution law on all 72 coordinates.
/-- Every array is its own inverse. -/
theorem generatedAxisGlobalTwelveOctadPermForward_involutive : ∀ k : Fin 3, ∀ i : Fin 24,
    generatedAxisGlobalTwelveOctadPermForward k (generatedAxisGlobalTwelveOctadPermForward k i) =
      i := by
  decide +kernel

/-- The three involutions as genuine coordinate permutations. -/
def generatedAxisGlobalTwelveOctadPermEquiv (k : Fin 3) : Equiv.Perm (Fin 24) where
  toFun := generatedAxisGlobalTwelveOctadPermForward k
  invFun := generatedAxisGlobalTwelveOctadPermForward k
  left_inv := generatedAxisGlobalTwelveOctadPermForward_involutive k
  right_inv := generatedAxisGlobalTwelveOctadPermForward_involutive k

/-- Code labels of the images of the twelve published Golay generators. -/
def generatedAxisGlobalTwelveOctadPermCodeImages : Fin 3 → Fin 12 → Fin 4096 :=
  ![![2613, 2614, 4, 2699, 1551, 32, 247, 1695, 816, 1055, 3715, 2048],
    ![2151, 2148, 2055, 323, 118, 1511, 1506, 1671, 1513, 1356, 2895, 2048],
    ![2275, 2272, 3008, 2059, 1292, 1561, 268, 3863, 907, 1428, 80, 2048]]

set_option maxHeartbeats 4000000 in
-- The 36 generator-image vectors are checked against the actual encoder.
/-- Each involution sends every published Golay generator to the displayed codeword. -/
theorem generatedAxisGlobalTwelveOctadPerm_code_certificate : ∀ k : Fin 3, ∀ j : Fin 12,
    golayPermute (generatedAxisGlobalTwelveOctadPermEquiv k) (golayEncoder (Pi.single j 1)) =
      golayEncoder (golayLabelCoefficients (generatedAxisGlobalTwelveOctadPermCodeImages k j)) := by
  decide +kernel

private def octadPermuteLinear (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem octadPermute_mem_of_generator_images (p : Equiv.Perm (Fin 24))
    (hp : ∀ j, golayPermute p (golayEncoder (Pi.single j 1)) ∈ golayCode)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) : golayPermute p c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change (octadPermuteLinear p).comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  exact golayCode.smul_mem _ (hp j)

/-- The three involutions are genuine Golay automorphisms. -/
def generatedAxisGlobalTwelveOctadPermutation (k : Fin 3) : golayAutomorphismSubgroup :=
  ⟨generatedAxisGlobalTwelveOctadPermEquiv k, by
    have hp : ∀ j, golayPermute (generatedAxisGlobalTwelveOctadPermEquiv k)
        (golayEncoder (Pi.single j 1)) ∈ golayCode := by
      intro j
      rw [generatedAxisGlobalTwelveOctadPerm_code_certificate k j]
      exact ⟨_, rfl⟩
    have hi : (generatedAxisGlobalTwelveOctadPermEquiv k)⁻¹ =
        generatedAxisGlobalTwelveOctadPermEquiv k := by
      ext i
      rfl
    intro c
    constructor
    · exact octadPermute_mem_of_generator_images _ hp c
    · intro hc
      have h := octadPermute_mem_of_generator_images _ hp _ hc
      rw [← golayPermute_mul] at h
      have hs : generatedAxisGlobalTwelveOctadPermEquiv k *
          generatedAxisGlobalTwelveOctadPermEquiv k = 1 := by
        ext i
        exact congrArg Fin.val (generatedAxisGlobalTwelveOctadPermForward_involutive k i)
      rw [hs, golayPermute_one] at h
      exact h⟩

/-- The genuine permutation agrees with its forward array. -/
theorem generatedAxisGlobalTwelveOctadPermutation_apply (k : Fin 3) (i : Fin 24) :
    (generatedAxisGlobalTwelveOctadPermutation k).val i =
      generatedAxisGlobalTwelveOctadPermForward k i := rfl

set_option maxHeartbeats 2000000 in
-- Check the block condition on all 72 coordinates.
/-- Each involution maps the physical octad-three block `{8, ..., 15}` onto itself. -/
theorem generatedAxisGlobalTwelveOctadPermForward_block : ∀ k : Fin 3, ∀ i : Fin 24,
    (8 ≤ (generatedAxisGlobalTwelveOctadPermForward k i).val ∧
      (generatedAxisGlobalTwelveOctadPermForward k i).val < 16) ↔ (8 ≤ i.val ∧ i.val < 16) := by
  decide +kernel

/-- Each involution preserves the complete integral octad-three coordinate section. -/
theorem generatedAxisGlobalTwelveOctadPermutation_preserves (k : Fin 3) :
    generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad)
      (golayPermutationIsometry (generatedAxisGlobalTwelveOctadPermutation k)) :=
  generatedAxisE8Orthogonal_permutation_preserves _
    (generatedAxisGlobalTwelveOctadPermForward_block k)

/-- Physical coordinate matrices of the three involutions. -/
def generatedAxisGlobalTwelveOctadPermPhysical (k : Fin 3) : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if generatedAxisGlobalTwelveOctadPermForward k j = i then 1 else 0

/-- Their exact integer actions in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveOctadPermIntegral : Fin 3 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![![![-1, -1, 2, -1, 3, -1, 3, 5, -1, 2, 2, 4, -1, 3, 5, 3, 0, 4, 2, 9, 2, 5, 4, -1],
      ![0, 0, 0, 1, -1, 0, -1, -1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0],
      ![0, 1, -1, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, -1, 0, -1, 0, -2, 0, -1, 0, 0],
      ![0, 0, -1, 0, -1, 0, -1, -2, 0, 0, -1, -1, 0, -1, -2, -1, 0, -1, -1, -2, -1, -1, -1, 0],
      ![0, 0, -1, 0, -1, 1, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0, -2, -1, -1, 0, 0],
      ![0, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0, -1, -1, -2, 0, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, -1, 0, 0, 0, -1, -1, 1, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, -2, 0, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0],
      ![0, 0, -1, 0, -1, 0, 0, -1, 0, -1, -1, -2, 0, -1, -1, -1, 0, -1, -1, -2, -1, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, 1, -1, -1, -1, 0, -1, -1, -2, 0, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0],
      ![2, 1, 0, 1, 0, 1, 0, -1, 1, 1, 1, 0, 1, 0, -1, 0, 1, -1, 0, -2, -1, -1, -1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    ![![7, 6, 3, 3, 3, 3, 6, 5, 6, 6, 6, 6, 6, 6, 6, 6, -25, -8, -11, -10, -11, -8, -8, 3],
      ![-2, -2, -1, -1, -1, -1, -1, -1, -2, -2, -1, -2, -1, -2, -1, -1, 5, 1, 2, 2, 2, 2, 2, -1],
      ![-2, -2, -1, -1, -1, 0, -1, -1, -1, -2, -2, -2, -1, -1, -1, -1, 4, 2, 2, 1, 2, 1, 2, -1],
      ![-2, -1, -1, -1, 0, -1, -2, -1, -1, -2, -1, -1, -2, -1, -1, -2, 5, 2, 3, 2, 3, 1, 2, -1],
      ![-2, -1, -1, 0, -1, -1, -2, -1, -2, -1, -2, -1, -1, -1, -2, -1, 5, 2, 2, 2, 3, 2, 2, -1],
      ![0, 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, -1, -1, -1, 5, 1, 2, 2, 2, 2, 1, 0],
      ![0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, -1, -1, -1, -1, -1, 6, 2, 3, 2, 2, 2, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1, -1, 0, -1, -1, -1, 0],
      ![-2, -1, -1, -1, -1, -1, -2, -1, -2, -2, -2, -2, -1, -1, -2, -2, 4, 1, 1, 1, 2, 1, 1, -1],
      ![0, -1, 0, 0, 0, 0, 0, -1, -1, -1, 0, -1, -1, -2, -1, -1, 5, 1, 2, 2, 1, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1, -2, 5, 1, 2, 1, 2, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 1, -2, 0, -1, 0, -1, 0, -1, 0],
      ![-2, -2, -1, -1, -1, -1, -1, -1, -2, -1, -2, -2, -2, -2, -2, -1, 4, 1, 1, 2, 1, 1, 1, -1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 0, -2, 0, 0, -1, 0, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, -2, -1, 0, 0, -1, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, -2, -1, -1, -1, 0, 0, 0, 0],
      ![-2, -2, -1, -1, -1, -1, -2, -2, -1, -1, -1, -1, -1, -1, -1, -1, 4, 1, 2, 2, 2, 1, 1, -1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1, -1, -1, -1, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, -2, 0, -1, 0, -1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1, -1, -1, -1, -1, -1, 0],
      ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 0, -1, 0, -1, -1, 0, -1, 2],
      ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, -2, 0, -1, -1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, -1, -1, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 2, 2, 2, 2, 1]],
    ![![-1, 2, 3, -1, -29, 0, -1, -10, -1, 2, -1, 3, 2, -11, -11, 3, 2, 3, -14, -9, -8, 6, -9, -1],
      ![0, 0, -1, 0, 6, 0, 0, 2, 0, -1, 0, -1, -1, 2, 2, -1, -1, -1, 3, 1, 1, -2, 2, 0],
      ![0, 0, 0, 0, 5, 0, 0, 2, 0, 0, 0, 0, -1, 2, 2, -1, -1, 0, 2, 2, 1, -1, 1, 0],
      ![0, -1, -1, 0, 6, 0, 1, 2, 0, 0, 0, -1, -1, 2, 2, 0, 0, 0, 3, 3, 1, -1, 2, 0],
      ![0, -1, 0, 0, 6, 0, 0, 2, 0, -1, 0, -1, 0, 2, 3, -1, 0, -1, 3, 2, 2, -1, 2, 0],
      ![2, 0, 0, 1, 6, 1, 1, 2, 1, 0, 1, -1, 1, 2, 2, 0, 1, -1, 3, 1, 1, -1, 2, 1],
      ![0, 0, -1, 1, 6, 0, 0, 3, 0, 0, 0, 0, 0, 3, 2, 0, -1, 0, 3, 2, 2, -1, 2, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, -1, 0],
      ![0, -1, -1, 0, 5, 0, 0, 1, 0, -1, 1, -1, -1, 1, 2, -1, 0, -1, 3, 2, 1, -2, 2, 0],
      ![0, 0, -1, 0, 5, 0, 0, 2, 0, -1, 0, -1, -1, 2, 1, -1, -1, -1, 2, 1, 1, -2, 1, 0],
      ![0, -1, 0, 0, 5, 0, 0, 2, 1, 0, 0, 0, -1, 2, 2, -1, 0, 0, 3, 2, 2, -1, 1, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, -1, -1, 0, 1, 0, 0],
      ![0, 0, 0, 0, 5, 0, 0, 2, 0, -1, 0, 0, 0, 2, 2, -1, -1, -1, 2, 1, 2, -1, 2, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 2, 0, 1, 0, 0, -1, 1, 0, 1, -1, 0, -1, 1, -1, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -1, -1, 1, 0, 0, -1, -1, -1, 0, -1, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, -1, 0, -1, 0],
      ![0, -1, -1, 0, 5, 0, 0, 1, 0, 0, 0, -1, 0, 2, 2, 0, -1, -1, 2, 1, 1, -1, 1, 0],
      ![0, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, -1, 0],
      ![0, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, -1, -1, 0, 1, 0, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, -1, 0, 0, 0],
      ![0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, -1, 0, -1, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0],
      ![0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 2, 0, 2, 1]]]

set_option maxHeartbeats 10000000 in
-- Verify all three integer lattice basis actions entry by entry.
/-- Every cached integer entry satisfies the actual basis transport equation. -/
theorem generatedAxisGlobalTwelveOctadPerm_integral : ∀ k : Fin 3,
    generatedAxisGlobalTwelveOctadPermPhysical k * leechBasisMatrix =
      leechBasisMatrix * generatedAxisGlobalTwelveOctadPermIntegral k := by
  decide +kernel

/-- The physical matrices act by the genuine coordinate permutations. -/
theorem generatedAxisGlobalTwelveOctadPerm_embedding (k : Fin 3) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalTwelveOctadPermutation k)).val
      (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (generatedAxisGlobalTwelveOctadPermPhysical k *ᵥ u) := by
  have hp : ∀ i j : Fin 24,
      generatedAxisGlobalTwelveOctadPermPhysical k i j =
        if (generatedAxisGlobalTwelveOctadPermutation k).val.symm i = j then 1 else 0 := by
    intro i j
    unfold generatedAxisGlobalTwelveOctadPermPhysical
    rw [← generatedAxisGlobalTwelveOctadPermutation_apply]
    have he : (generatedAxisGlobalTwelveOctadPermutation k).val j = i ↔
        (generatedAxisGlobalTwelveOctadPermutation k).val.symm i = j := by
      exact (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- The cached integral basis action is the full actual lattice action. -/
theorem generatedAxisGlobalTwelveOctadPerm_basis (k : Fin 3) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalTwelveOctadPermutation k)).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ
        (generatedAxisGlobalTwelveOctadPermIntegral k *ᵥ u)) := by
  rw [generatedAxisGlobalTwelveOctadPerm_embedding, Matrix.mulVec_mulVec,
    generatedAxisGlobalTwelveOctadPerm_integral, ← Matrix.mulVec_mulVec]

/-- Binary column masks in the actual published hyperbolic coordinates. -/
def generatedAxisGlobalTwelveOctadPermColumns : Fin 3 → Fin 24 → ℕ :=
  ![![5999157, 7506486, 2686980, 1129099, 4511247, 274464, 2294007, 1070751, 4764464, 287775,
      1130115, 2048, 7180288, 7184384, 2977792, 2719744, 3944448, 1454080, 262144, 5013504,
      1048576, 5877760, 6881280, 12627968],
    ![1742951, 7448676, 2459655, 8155459, 5595254, 2233831, 3786210, 7116423, 4568553, 7267660,
      7973711, 2048, 5951488, 5230592, 7041024, 7340032, 65536, 1519616, 7843840, 1966080,
      7766016, 4718592, 4063232, 12611584],
    ![6904035, 26848, 5684160, 7292939, 1217804, 771609, 2670860, 1482519, 2704267, 5543316,
      2150480, 2048, 1740800, 1609728, 2949120, 1540096, 6946816, 12288, 4222976, 3174400,
      4014080, 1720320, 2818048, 8974336]]

set_option maxHeartbeats 16000000 in
-- Bind all displayed coordinate bits to the genuine binary basis matrices.
/-- Every compact mask column is the actual binary basis-matrix column. -/
theorem generatedAxisGlobalTwelveOctadPermColumns_certificate : ∀ k : Fin 3,
    leechHyperbolicInverse *
        (generatedAxisGlobalTwelveOctadPermIntegral k).map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveOctadPermColumns k) := by
  decide +kernel

/-- The compact columns give the genuine Conway quotient action of each involution. -/
theorem generatedAxisGlobalTwelveOctadPerm_binary (k : Fin 3) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup
      (golayPermutationIsometry (generatedAxisGlobalTwelveOctadPermutation k))) v =
        generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveOctadPermColumns k) *ᵥ v := by
  change leechBinaryAction _ v = _
  rw [leechBinaryAction_of_basis_certificate _ _ (generatedAxisGlobalTwelveOctadPerm_basis k) v,
    generatedAxisGlobalTwelveOctadPermColumns_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
