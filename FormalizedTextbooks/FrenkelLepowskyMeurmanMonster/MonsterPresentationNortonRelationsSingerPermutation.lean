/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The explicit coordinate permutation p43549632 suggested by Norton’s Singer normalizer.
The arrays were discovered with the public BSD-2-Clause mmgroup runtime;
the inverse laws and Golay-generator images below are checked by Lean's kernel.
Only the stated finite mathematical permutations and their images are used.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Forward coordinate arrays, in the order of the source discovery labels. -/
def monsterNortonSingerPermForward : Fin 1 → Fin 24 → Fin 24 :=
![![4, 7, 5, 6, 8, 9, 10, 11, 0, 2, 3, 1,
    16, 17, 18, 19, 20, 23, 21, 22, 12, 14, 15, 13]]

/-- Explicit inverse arrays. -/
def monsterNortonSingerPermInverse : Fin 1 → Fin 24 → Fin 24 :=
![![8, 11, 9, 10, 0, 2, 3, 1, 4, 5, 6, 7,
    20, 23, 21, 22, 12, 13, 14, 15, 16, 18, 19, 17]]

/-- Each finite array defines a genuine coordinate permutation. -/
def monsterNortonSingerPermutation (k : Fin 1) : Equiv.Perm (Fin 24) where
  toFun := monsterNortonSingerPermForward k
  invFun := monsterNortonSingerPermInverse k
  left_inv := by
    have h : ∀ k i, monsterNortonSingerPermInverse k (monsterNortonSingerPermForward k i) = i := by
      decide +kernel
    exact h k
  right_inv := by
    have h : ∀ k i, monsterNortonSingerPermForward k (monsterNortonSingerPermInverse k i) = i := by
      decide +kernel
    exact h k

/-- Generator image labels for the physical permutation and its inverse. -/
def monsterNortonSingerPermCodeImages : Fin 2 → Fin 12 → Fin 4096 :=
![![15, 2059, 2055, 2061, 512, 768, 16, 32, 192, 64, 3087, 2048],
  ![2062, 2057, 2051, 2053, 64, 128, 512, 768, 48, 16, 3073, 2048]]

set_option maxHeartbeats 2000000 in
-- The 24 generator-image vectors are checked against the actual encoder.
theorem monsterNortonSingerPermutation_code_certificate :
    ∀ k : Fin 1, ∀ j : Fin 12,
      golayPermute (monsterNortonSingerPermutation k) (golayEncoder (Pi.single j 1)) =
        golayEncoder (golayLabelCoefficients
          (monsterNortonSingerPermCodeImages (Fin.castAdd 1 k) j)) ∧
      golayPermute (monsterNortonSingerPermutation k)⁻¹ (golayEncoder (Pi.single j 1)) =
        golayEncoder (golayLabelCoefficients
          (monsterNortonSingerPermCodeImages (Fin.natAdd 1 k) j)) := by
  decide +kernel

private def golayPermuteLinear (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem golayPermute_mem_of_generator_images (p : Equiv.Perm (Fin 24))
    (hp : ∀ j, golayPermute p (golayEncoder (Pi.single j 1)) ∈ golayCode)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) : golayPermute p c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change (golayPermuteLinear p).comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  exact golayCode.smul_mem _ (hp j)

/-- The explicit finite permutations preserve the actual Golay code. -/
def monsterNortonSingerGolayPermutation (k : Fin 1) : golayAutomorphismSubgroup :=
  ⟨monsterNortonSingerPermutation k, by
    have hp : ∀ j, golayPermute (monsterNortonSingerPermutation k)
        (golayEncoder (Pi.single j 1)) ∈ golayCode := by
      intro j
      rw [(monsterNortonSingerPermutation_code_certificate k j).1]
      exact ⟨_, rfl⟩
    have hq : ∀ j, golayPermute (monsterNortonSingerPermutation k)⁻¹
        (golayEncoder (Pi.single j 1)) ∈ golayCode := by
      intro j
      rw [(monsterNortonSingerPermutation_code_certificate k j).2]
      exact ⟨_, rfl⟩
    intro c
    constructor
    · exact golayPermute_mem_of_generator_images _ hp c
    · intro hc
      have h := golayPermute_mem_of_generator_images _ hq _ hc
      rw [golayPermute_inv] at h
      exact h⟩

/-- The corresponding genuine isometries of the actual Leech lattice. -/
def monsterNortonSingerPermutationIsometry (k : Fin 1) : leechIsomSubgroup :=
  golayPermutationIsometry (monsterNortonSingerGolayPermutation k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
