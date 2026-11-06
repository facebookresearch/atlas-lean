/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Two explicit coordinate permutations used for the Ω orbit-span certificate.
Their arrays were discovered with the public BSD-2-Clause mmgroup runtime;
the inverse laws and Golay-generator images below are checked by Lean's kernel.
Only the stated finite mathematical permutations and their images are used.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Forward coordinate arrays, in the order of the source discovery labels. -/
def omegaOrbitPermForward : Fin 2 → Fin 24 → Fin 24 :=
![![15, 3, 20, 16, 11, 4, 6, 5, 7, 8,
    9, 10, 12, 0, 21, 18, 14, 22, 19, 2,
    13, 17, 1, 23],
  ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6,
    10, 14, 3, 7, 11, 15, 20, 17, 18, 19,
    16, 21, 23, 22]]

/-- Explicit inverse arrays. -/
def omegaOrbitPermInverse : Fin 2 → Fin 24 → Fin 24 :=
![![13, 22, 19, 1, 5, 7, 6, 8, 9, 10,
    11, 4, 12, 20, 16, 0, 3, 21, 15, 18,
    2, 14, 17, 23],
  ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6,
    10, 14, 3, 7, 11, 15, 20, 17, 18, 19,
    16, 21, 23, 22]]

/-- Each finite array defines a genuine coordinate permutation. -/
def omegaOrbitPermutation (k : Fin 2) : Equiv.Perm (Fin 24) where
  toFun := omegaOrbitPermForward k
  invFun := omegaOrbitPermInverse k
  left_inv := by
    have h : ∀ k i, omegaOrbitPermInverse k (omegaOrbitPermForward k i) = i := by
      decide +kernel
    exact h k
  right_inv := by
    have h : ∀ k i, omegaOrbitPermForward k (omegaOrbitPermInverse k i) = i := by
      decide +kernel
    exact h k

/-- Generator image labels for both forward permutations, then both inverses. -/
def omegaOrbitPermCodeImages : Fin 4 → Fin 12 → Fin 4096 :=
![![4093, 782, 2316, 2572, 816, 2593, 960, 2383, 12, 2052,
    2046, 2048],
  ![684, 1020, 1028, 1032, 16, 64, 32, 128, 51, 205,
    1024, 2048],
  ![3343, 270, 2560, 2816, 3131, 3111, 3205, 3273, 2308, 2312,
    1106, 2048],
  ![684, 1020, 1028, 1032, 16, 64, 32, 128, 51, 205,
    1024, 2048]]

set_option maxHeartbeats 2000000 in
-- The 48 generator-image vectors are checked against the actual encoder.
theorem omegaOrbitPermutation_code_certificate :
    ∀ k : Fin 2, ∀ j : Fin 12,
      golayPermute (omegaOrbitPermutation k) (golayEncoder (Pi.single j 1)) =
        golayEncoder (golayLabelCoefficients (omegaOrbitPermCodeImages (Fin.castAdd 2 k) j)) ∧
      golayPermute (omegaOrbitPermutation k)⁻¹ (golayEncoder (Pi.single j 1)) =
        golayEncoder (golayLabelCoefficients (omegaOrbitPermCodeImages (Fin.natAdd 2 k) j)) := by
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
def omegaOrbitGolayPermutation (k : Fin 2) : golayAutomorphismSubgroup :=
  ⟨omegaOrbitPermutation k, by
    have hp : ∀ j, golayPermute (omegaOrbitPermutation k)
        (golayEncoder (Pi.single j 1)) ∈ golayCode := by
      intro j
      rw [(omegaOrbitPermutation_code_certificate k j).1]
      exact ⟨_, rfl⟩
    have hq : ∀ j, golayPermute (omegaOrbitPermutation k)⁻¹
        (golayEncoder (Pi.single j 1)) ∈ golayCode := by
      intro j
      rw [(omegaOrbitPermutation_code_certificate k j).2]
      exact ⟨_, rfl⟩
    intro c
    constructor
    · exact golayPermute_mem_of_generator_images _ hp c
    · intro hc
      have h := golayPermute_mem_of_generator_images _ hq _ hc
      rw [golayPermute_inv] at h
      exact h⟩

/-- The corresponding genuine isometries of the actual Leech lattice. -/
def omegaOrbitPermutationIsometry (k : Fin 2) : leechIsomSubgroup :=
  golayPermutationIsometry (omegaOrbitGolayPermutation k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
