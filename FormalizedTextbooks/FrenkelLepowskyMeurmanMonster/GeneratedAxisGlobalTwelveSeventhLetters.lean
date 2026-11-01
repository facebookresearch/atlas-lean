/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTriangleMembership
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationProjection
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhExact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlanePermutation
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskInverse
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiBinary
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Four letters for the Seventh binary forest: three explicit triangle-compatible Golay
permutations and the corrected moving Xi of the Seventh exact-order proof. Each lies in the
projected Seventh-axis stabilizer, and each acts on the binary Leech quotient by kernel-checked
packed columns in the hyperbolic coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Forward coordinate tables of the three triangle permutations. -/
def seventhForestPermForward : Fin 3 → Fin 24 → Fin 24 :=
  ![![7, 20, 8, 1, 6, 11, 3, 23, 21, 9, 5, 2, 15, 12, 18, 13, 16, 19, 14, 17, 22, 10, 4, 0],
   ![6, 20, 0, 9, 2, 7, 23, 10, 5, 11, 22, 1, 13, 18, 12, 14, 16, 17, 15, 19, 3, 21, 8, 4],
   ![4, 11, 2, 20, 0, 5, 8, 23, 6, 21, 10, 1, 12, 18, 14, 15, 19, 17, 13, 16, 3, 9, 22, 7]]

/-- Inverse coordinate tables of the three triangle permutations. -/
def seventhForestPermInverse : Fin 3 → Fin 24 → Fin 24 :=
  ![![23, 3, 11, 6, 22, 10, 4, 0, 2, 9, 21, 5, 13, 15, 18, 12, 16, 19, 14, 17, 1, 8, 20, 7],
   ![2, 11, 4, 20, 23, 8, 0, 5, 22, 3, 7, 9, 14, 12, 15, 18, 16, 17, 13, 19, 1, 21, 10, 6],
   ![4, 11, 2, 20, 0, 5, 8, 23, 6, 21, 10, 1, 12, 18, 14, 15, 19, 17, 13, 16, 3, 9, 22, 7]]

/-- The three coordinate permutations. -/
def seventhForestPerm (k : Fin 3) : Equiv.Perm (Fin 24) where
  toFun := seventhForestPermForward k
  invFun := seventhForestPermInverse k
  left_inv := by
    have h : ∀ k i, seventhForestPermInverse k (seventhForestPermForward k i) = i := by
      decide +kernel
    exact h k
  right_inv := by
    have h : ∀ k i, seventhForestPermForward k (seventhForestPermInverse k i) = i := by
      decide +kernel
    exact h k

/-- Golay labels of the generator images under the three permutations, then their inverses. -/
def seventhForestPermCodeImages : Fin 6 → Fin 12 → Fin 4096 :=
  ![![2969, 3531, 3533, 486, 2639, 2610, 1839, 3133, 2337, 1317, 1421, 2048],
   ![488, 1178, 1180, 918, 1292, 1343, 35, 238, 3101, 25, 3420, 2048],
   ![2967, 3637, 3635, 2535, 1508, 1492, 21, 128, 1752, 44, 3514, 2048],
   ![2528, 4018, 4020, 2681, 138, 147, 3076, 3306, 115, 1931, 1204, 2048],
   ![2535, 3637, 3635, 2967, 112, 1938, 3168, 227, 135, 26, 1331, 2048],
   ![2967, 3637, 3635, 2535, 1508, 1492, 21, 128, 1752, 44, 3514, 2048]]

set_option maxHeartbeats 4000000 in
-- The 72 generator-image vectors are checked against the actual encoder.
/-- Each permutation and its inverse send the Golay generators to the displayed codewords. -/
theorem seventhForestPerm_code_certificate : ∀ k : Fin 3, ∀ j : Fin 12,
    golayPermute (seventhForestPerm k) (golayEncoder (Pi.single j 1)) =
      golayEncoder (golayLabelCoefficients (seventhForestPermCodeImages (Fin.castAdd 3 k) j)) ∧
    golayPermute (seventhForestPerm k)⁻¹ (golayEncoder (Pi.single j 1)) =
      golayEncoder (golayLabelCoefficients (seventhForestPermCodeImages (Fin.natAdd 3 k) j)) := by
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

/-- The three permutations are genuine Golay automorphisms. -/
def seventhForestGolayPerm (k : Fin 3) : golayAutomorphismSubgroup :=
  ⟨seventhForestPerm k, by
    have hp : ∀ j, golayPermute (seventhForestPerm k) (golayEncoder (Pi.single j 1)) ∈
        golayCode := by
      intro j
      rw [(seventhForestPerm_code_certificate k j).1]
      exact ⟨_, rfl⟩
    have hq : ∀ j, golayPermute (seventhForestPerm k)⁻¹ (golayEncoder (Pi.single j 1)) ∈
        golayCode := by
      intro j
      rw [(seventhForestPerm_code_certificate k j).2]
      exact ⟨_, rfl⟩
    intro c
    constructor
    · exact golayPermute_mem_of_generator_images _ hp c
    · intro hc
      have h := golayPermute_mem_of_generator_images _ hq _ hc
      rw [golayPermute_inv] at h
      exact h⟩

set_option maxHeartbeats 4000000 in
-- The three permutations preserve the seventh section octad (label six).
private theorem perm_octad (k : Fin 3) :
    golayPermute (seventhForestGolayPerm k).val (golayOctadWord generatedSeventhSectionOctad) =
      golayOctadWord generatedSeventhSectionOctad := by
  rw [golayOctadWord, generatedSeventh_section_octad_label]
  revert k
  decide +kernel

/-- The three permutations lie in the actual triangle permutation subgroup. -/
theorem seventhForestGolayPerm_triangle (k : Fin 3) :
    seventhForestGolayPerm k ∈ generatedSeventhTrianglePermutationSubgroup := by
  rw [generatedSeventh_triangle_permutation_mem_iff]
  refine ⟨perm_octad k, ?_⟩
  rw [generatedSeventhTriangleCoordinates, Finset.smul_finset_def,
    Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  change ({seventhForestPermForward k 16, seventhForestPermForward k 17,
    seventhForestPermForward k 19} : Finset (Fin 24)) = _
  revert k
  decide +kernel

/-- The physical coordinate matrices of the three permutations. -/
def seventhForestPermPhysical (k : Fin 3) : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if seventhForestPermForward k j = i then 1 else 0

/-- Integral lattice-basis matrices of the three permutations. -/
def seventhForestPermIntegral : Fin 3 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![![![5, 6, 2, 2, 2, 5, 2, -11, 5, 2, 2, 3, 5, 6, 4, 4, 2, 5, 4, 0, 5, 3, 3, 2],
     ![-2, -2, -1, 0, -1, -2, -1, 2, -2, -1, -1, -1, -1, -2, -1, -1, -1, -1, -1, 0, -1, -1, -1,
       -1],
     ![-2, -2, -1, -1, -1, -2, -1, 1, -2, -1, -1, -1, -1, -2, -1, -1, -1, -2, -2, 0, -1, -1, -1,
       -1],
     ![-2, -2, -1, -1, -1, -2, 0, 2, -1, -1, -1, -1, -2, -2, -1, -1, -1, -1, -1, 0, -1, -1, -1,
       -1],
     ![-2, -2, -1, -1, -1, -1, -1, 2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, -1, -1, 0,
       -1],
     ![-2, -1, -1, -1, -1, -1, -1, 2, -1, -1, 0, 0, -2, -1, -1, -1, -1, 0, 0, 0, -1, -1, 0, -1],
     ![-2, -1, -1, -1, 0, -1, -1, 3, -2, -1, -1, -1, -2, -1, -1, -1, -1, -1, -1, 0, -1, -1, 0,
       -1],
     ![4, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 1, 2, 1, 1, 1, 2, 0, 1, 0, 0, 1, 0, 2],
     ![0, -1, 1, 0, 0, -1, 0, 2, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, 0],
     ![0, 0, 0, 0, 0, -1, 0, 2, -1, 1, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0],
     ![0, 0, 0, 0, 0, -1, 0, 2, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0],
     ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0],
     ![0, -1, 0, 0, 0, 0, 0, 2, -1, 0, 0, -1, -1, -1, -1, -1, 0, -1, -1, 0, -2, -1, -1, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0],
     ![0, -1, 0, 0, 0, 0, 0, 2, -1, 0, 0, -1, 0, -1, -1, 0, 1, -1, 0, 0, -1, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
     ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    ![![-1, 3, 0, -1, -1, 2, -29, -12, -1, 2, 3, 4, 2, 6, -12, -8, -1, -9, 3, -10, 2, -9, -9, -1],
     ![0, -1, 0, 0, 0, -1, 6, 2, 0, -1, -1, -1, -1, -2, 2, 1, 0, 1, -1, 2, -1, 1, 1, 0],
     ![0, -1, 0, 0, 1, -1, 5, 2, 0, -1, 0, -1, 0, -1, 3, 1, 0, 1, 0, 2, 0, 1, 2, 0],
     ![0, -1, 0, 0, 0, -1, 6, 2, 0, -1, 0, -1, 0, -2, 3, 2, 0, 1, -1, 2, 0, 2, 2, 0],
     ![0, -1, 0, 0, 0, -1, 6, 2, 0, 0, -1, -1, -1, -2, 2, 1, 0, 2, -1, 2, -1, 2, 1, 0],
     ![0, 0, 0, 0, 0, -1, 5, 2, 1, 0, -1, 0, -1, -1, 2, 1, 0, 2, -1, 2, 0, 2, 1, 0],
     ![2, 1, 1, 1, 1, 0, 7, 3, 1, 1, 0, 0, 1, 0, 3, 2, 1, 2, -1, 2, 0, 3, 2, 1],
     ![0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, -1, 0, -1, 0, 0],
     ![0, -1, 0, 0, 0, 0, 5, 2, 0, -1, 0, -1, -1, -2, 2, 1, 0, 1, 0, 2, -1, 1, 2, 0],
     ![0, 0, 0, 1, 0, 0, 5, 3, 0, -1, 0, 0, -1, -1, 2, 2, 0, 2, 0, 2, 0, 1, 2, 0],
     ![0, 0, 0, 0, 0, 0, 5, 3, 0, -1, -1, -1, 0, -1, 2, 1, 0, 2, -1, 1, 0, 2, 2, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0],
     ![0, -1, 0, 0, 0, 0, 5, 2, 0, 0, -1, -1, -1, -1, 2, 1, 0, 2, -1, 2, -1, 1, 1, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, 2, 1, 0, 0, 0, -1, 0, -1, 1, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, -1, 0, -1, -1, 0],
     ![0, -1, 0, 0, 0, 0, 5, 2, 0, 0, -1, -1, 0, -1, 2, 2, 1, 2, 0, 2, 0, 2, 2, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, 0, 1, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1, -1, 0],
     ![0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, 0, 0, -1, 1, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0],
     ![0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 2, 1, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1, 0, 0],
     ![0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 1]],
    ![![-1, 2, -1, 3, 0, -1, -1, -12, -1, 2, -1, 3, -1, 3, 0, 3, 3, 7, 4, 4, 4, 3, 4, -1],
     ![0, -1, 0, -1, 0, 0, 0, 2, 0, -1, 0, -1, 0, -1, 0, -1, 0, -2, -1, -1, -1, -1, -1, 0],
     ![0, -1, 1, -1, 0, 0, 0, 2, 0, -1, 0, -1, 0, -1, 0, -1, -1, -2, -1, -1, -1, -1, -1, 0],
     ![0, -1, 0, -1, 0, 0, 0, 2, 0, 0, 0, -1, 0, -1, 0, -1, -1, -2, -1, -1, -1, -1, -1, 0],
     ![2, 1, 1, 0, 1, 1, 1, 3, 1, 1, 1, 0, 1, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1, 1],
     ![0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 3, 1, -1, 0, 0, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, -1, 0, -1, 0, 0, 1, 2, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0],
     ![0, -1, 0, 0, 0, 0, 0, 2, 0, -1, 0, -1, 0, -1, 0, -1, -1, -2, -1, -1, -1, -1, -1, 0],
     ![0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0],
     ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0],
     ![0, 0, 0, -1, 0, 0, 0, 2, 0, -1, 0, -1, 1, 0, 0, -1, 0, -1, -1, -1, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, -1, 0, 0, 0, 2, 0, -1, 0, -1, 0, -1, 0, -1, -1, -2, -1, -1, -1, -1, -1, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 1, 1, 1, 0],
     ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
     ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

set_option maxHeartbeats 20000000 in
-- Verify the full integer lattice basis actions entry by entry.
/-- The integral matrices satisfy the actual basis transport equations. -/
theorem seventhForestPerm_integral : ∀ k : Fin 3,
    seventhForestPermPhysical k * leechBasisMatrix =
      leechBasisMatrix * seventhForestPermIntegral k := by
  decide +kernel

/-- The permutation isometries act on physical coordinates by the physical matrices. -/
theorem seventhForestPerm_embedding (k : Fin 3) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (seventhForestGolayPerm k)).val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (seventhForestPermPhysical k *ᵥ u) := by
  have hp : ∀ i j : Fin 24, seventhForestPermPhysical k i j =
      if (seventhForestGolayPerm k).val.symm i = j then 1 else 0 := by
    intro i j
    unfold seventhForestPermPhysical
    have he : seventhForestPermForward k j = i ↔ (seventhForestGolayPerm k).val.symm i = j := by
      change (seventhForestGolayPerm k).val j = i ↔ _
      exact (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- The integral matrices are the actual permutation actions on the lattice basis. -/
theorem seventhForestPerm_basis (k : Fin 3) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (seventhForestGolayPerm k)).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (seventhForestPermIntegral k *ᵥ u)) := by
  rw [seventhForestPerm_embedding, Matrix.mulVec_mulVec, seventhForestPerm_integral,
    ← Matrix.mulVec_mulVec]

/-- Packed binary columns of the three permutations in the hyperbolic coordinates. -/
def seventhForestPermColumns : Fin 3 → Fin 24 → ℕ :=
  ![![5512089, 4971979, 1621453, 6349286, 4131407, 1456690, 2008879, 2694205, 3377441, 7169317,
     1594765, 2048, 3309568, 3874816, 4472832, 2719744, 5431296, 5828608, 1609728, 7041024,
     2125824, 2154496, 7102464, 9236480],
   ![2781672, 2569370, 4936860, 299926, 3704076, 5690687, 2007075, 2556142, 7629853, 7008281,
     707932, 2048, 5828608, 8048640, 1093632, 2097152, 6545408, 5074944, 856064, 1740800,
     4362240, 188416, 4612096, 8712192],
   ![1280919, 7458357, 372275, 7305703, 8320484, 7181780, 4964373, 1540224, 603864, 237612,
     503226, 2048, 323584, 4247552, 2600960, 7340032, 5664768, 6414336, 1277952, 6000640,
     4427776, 1077248, 5464064, 12644352]]

set_option maxHeartbeats 20000000 in
-- The packed columns are the reduced integral matrices in hyperbolic coordinates.
/-- The packed columns are exactly the binary hyperbolic matrices of the permutations. -/
theorem seventhForestPermColumns_certificate : ∀ k : Fin 3,
    generatedAxisGlobalMaskColumnMatrix (seventhForestPermColumns k) =
      leechHyperbolicInverse * (seventhForestPermIntegral k).map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix := by
  decide +kernel

/-- The three permutations act on the binary quotient by their packed columns. -/
theorem seventhForestPerm_binary (k : Fin 3) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup
      (golayPermutationIsometry (seventhForestGolayPerm k))) v =
        generatedAxisGlobalMaskColumnMatrix (seventhForestPermColumns k) *ᵥ v := by
  rw [seventhForestPermColumns_certificate]
  exact leechBinaryAction_of_basis_certificate _ _ (seventhForestPerm_basis k) v

/-- The physical coordinate matrix of the moving-Xi conjugating permutation. -/
def seventhForestXiPermPhysical : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if generatedSeventhXiPlaneForward j = i then 1 else 0

/-- Integral lattice-basis matrix of the moving-Xi conjugating permutation. -/
def seventhForestXiPermIntegral : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![5, 5, 5, 2, 3, 6, 2, 5, 2, 6, 5, 6, 2, 7, 3, 5, 5, 7, 7, 5, -11, 6, 5, 2],
   ![-2, -1, -1, -1, -1, -2, -1, -1, -1, -2, -2, -1, -1, -2, -1, -2, -1, -1, -2, -1, 3, -1, -1,
     -1],
   ![0, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, -1, -1, 2, 0, -1, 0],
   ![0, -1, 0, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, -1, 0, -1, -1, -2, -2, -1, 2, -1, -2, 0],
   ![-2, -2, -2, -1, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -1, -1, -2, -1, -1, 2, -2, -1,
     -1],
   ![-2, -2, -1, -1, -1, -1, -1, -1, 0, -2, -1, -1, -1, -1, 0, -1, -2, -1, -1, -1, 2, -2, -1, -1],
   ![0, 0, -1, 0, 0, 0, 1, 0, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1, -1, 2, -1, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
   ![-2, -2, -2, -1, -1, -2, -1, -2, -1, -1, -2, -2, 0, -1, -1, -1, -1, -1, -2, -1, 2, -1, -1,
     -1],
   ![-2, -1, -1, -1, -1, -1, -1, 0, -1, -1, -2, -1, -1, -1, -1, -1, -2, -1, -2, -1, 2, -1, -1,
     -1],
   ![0, -1, -1, 0, 0, 0, 0, -1, 0, -1, -1, -2, 0, -1, -1, -1, -1, -2, -1, -2, 1, -2, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 1, 1, -1, 0, 1, 0],
   ![-2, -1, -2, 0, -1, -2, -1, -1, -1, -2, -1, -1, -1, -2, -1, -1, -2, -1, -1, -1, 2, -2, -1,
     -1],
   ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 0, 1, 0, -1, 1, 0, 2],
   ![0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 1, 1, 0],
   ![0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -2, 0, -1, 0, -2, -1, 0, 2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0],
   ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0],
   ![0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, -1, 0, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, -1, 1, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1]]

set_option maxHeartbeats 20000000 in
-- Verify the full integer lattice basis action entry by entry.
/-- The integral matrix satisfies the actual basis transport equation. -/
theorem seventhForestXiPerm_integral :
    seventhForestXiPermPhysical * leechBasisMatrix =
      leechBasisMatrix * seventhForestXiPermIntegral := by
  decide +kernel

/-- The conjugating permutation isometry acts on physical coordinates by its matrix. -/
theorem seventhForestXiPerm_embedding (u : Fin 24 → ℤ) :
    (golayPermutationIsometry generatedSeventhXiPlanePermutation).val
      (leechCoordinateEmbedding u) =
        leechCoordinateEmbedding (seventhForestXiPermPhysical *ᵥ u) := by
  have hp : ∀ i j : Fin 24, seventhForestXiPermPhysical i j =
      if generatedSeventhXiPlanePermutation.val.symm i = j then 1 else 0 := by
    intro i j
    unfold seventhForestXiPermPhysical
    rw [← generatedSeventhXiPlanePermutation_forward]
    have he : generatedSeventhXiPlanePermutation.val j = i ↔
        generatedSeventhXiPlanePermutation.val.symm i = j :=
      (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- The integral matrix is the actual conjugating permutation action on the lattice basis. -/
theorem seventhForestXiPerm_basis (u : Fin 24 → ℤ) :
    (golayPermutationIsometry generatedSeventhXiPlanePermutation).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (seventhForestXiPermIntegral *ᵥ u)) := by
  rw [seventhForestXiPerm_embedding, Matrix.mulVec_mulVec, seventhForestXiPerm_integral,
    ← Matrix.mulVec_mulVec]

/-- Packed binary columns of the conjugating permutation. -/
def seventhForestXiPermColumns : Fin 24 → ℕ :=
  ![871794, 1265420, 1247238, 3067618, 6312667, 4506571, 6332859, 3018999, 5644749, 7190057,
    7007299, 2048, 585728, 4251648, 4182016, 1798144, 5074944, 6545408, 4362240, 397312, 7954432,
    5570560, 4612096, 11194368]

/-- Packed binary columns of the inverse of the conjugating permutation. -/
def seventhForestXiPermInverseColumns : Fin 24 → ℕ :=
  ![2689245, 7603515, 4439359, 6719591, 2126652, 5827820, 3839636, 6854941, 1073932, 7178532,
    7800690, 2048, 8323072, 5230592, 1597440, 3612672, 856064, 2920448, 6000640, 2064384,
    1454080, 2334720, 6336512, 12644352]

/-- Packed binary columns of the corrected moving Xi. -/
def seventhForestXiPlaneColumns : Fin 24 → ℕ :=
  ![3539863, 13576413, 14295259, 6098952, 3647510, 9598965, 10737557, 1411206, 1646830, 721022,
    16723791, 4612096, 6144, 1271564, 1802, 3148694, 3115496, 2196368, 2591632, 330360, 918142,
    1933806, 5439494, 13181145]

set_option maxHeartbeats 20000000 in
-- The packed columns are the reduced integral matrix in hyperbolic coordinates.
/-- The packed columns are exactly the binary hyperbolic matrix of the permutation. -/
theorem seventhForestXiPermColumns_certificate :
    generatedAxisGlobalMaskColumnMatrix seventhForestXiPermColumns =
      leechHyperbolicInverse * seventhForestXiPermIntegral.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- The forward columns send every proposed inverse column to its coordinate unit.
/-- The proposed inverse columns invert the conjugating permutation on the binary quotient. -/
theorem seventhForestXiPermInverse_certificate : ∀ j : Fin 24,
    generatedAxisGlobalMaskColumnAction seventhForestXiPermColumns
      (seventhForestXiPermInverseColumns j) = 2 ^ j.val := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- The moving-Xi columns are the conjugate of the Xi matrix by the permutation matrix.
/-- The packed moving-Xi columns are the conjugated binary matrix. -/
theorem seventhForestXiPlaneColumns_certificate :
    generatedAxisGlobalMaskColumnMatrix seventhForestXiPlaneColumns =
      generatedAxisGlobalMaskColumnMatrix seventhForestXiPermColumns *
        (leechHyperbolicInverse * co1XiBasisMatrix.map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) *
        generatedAxisGlobalMaskColumnMatrix seventhForestXiPermInverseColumns := by
  decide +kernel

/-- The four Seventh forest letters, as actual elements of the Conway quotient. -/
def seventhForestLetter (k : Fin 4) : Co1 :=
  if h : k.val < 3 then
    QuotientGroup.mk' signsSubgroup (golayPermutationIsometry (seventhForestGolayPerm ⟨k.val, h⟩))
  else QuotientGroup.mk' signsSubgroup generatedSeventhXiPlaneFiber.val.2

/-- Every letter lies in the projected Seventh-axis stabilizer. -/
theorem seventhForestLetter_mem (k : Fin 4) :
    seventhForestLetter k ∈ generatedSeventhProjectedAxisStabilizer := by
  by_cases h : k.val < 3
  · simp only [seventhForestLetter, h, ↓reduceDIte]
    exact generatedSeventh_permutation_mem_projected _ (seventhForestGolayPerm_triangle _)
  · simp only [seventhForestLetter, h, ↓reduceDIte]
    exact generatedSeventhXiPlane_projected

/-- Packed binary columns of the four letters. -/
def seventhForestLetterColumns (k : Fin 4) : Fin 24 → ℕ :=
  if h : k.val < 3 then seventhForestPermColumns ⟨k.val, h⟩ else seventhForestXiPlaneColumns

/-- The corrected moving Xi has the stated spatial factorization. -/
theorem seventhForestXiPlane_spatial :
    generatedSeventhXiPlaneFiber.val.2 =
      golayPermutationIsometry generatedSeventhXiPlanePermutation * co1XiIsometry *
        (golayPermutationIsometry generatedSeventhXiPlanePermutation)⁻¹ := by
  have h1 : (localFiberIncl generatedSeventhXiPlaneCorrection).val.2 = 1 := rfl
  have h2 : xiSpinLocalFiber.val.2 = co1XiIsometry := rfl
  rw [← generatedSeventhXiPlanePermutationFiber_spatial, generatedSeventhXiPlaneFiber]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, h1, h2, one_mul]

/-- Every letter acts on the binary quotient by its packed columns. -/
theorem seventhForestLetter_binary (k : Fin 4) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (seventhForestLetter k) v =
      generatedAxisGlobalMaskColumnMatrix (seventhForestLetterColumns k) *ᵥ v := by
  by_cases h : k.val < 3
  · simp only [seventhForestLetter, seventhForestLetterColumns, h, ↓reduceDIte]
    exact seventhForestPerm_binary _ v
  · simp only [seventhForestLetter, seventhForestLetterColumns, h, ↓reduceDIte]
    have hP : ∀ w, co1BinaryAction (QuotientGroup.mk' signsSubgroup
        (golayPermutationIsometry generatedSeventhXiPlanePermutation)) w =
          generatedAxisGlobalMaskColumnMatrix seventhForestXiPermColumns *ᵥ w := by
      intro w
      rw [seventhForestXiPermColumns_certificate]
      exact leechBinaryAction_of_basis_certificate _ _ seventhForestXiPerm_basis w
    have hcol : ∀ j, generatedAxisGlobalMaskColumnMatrix seventhForestXiPermColumns *ᵥ
        monsterCo1GeometryBinaryMaskDecode (seventhForestXiPermInverseColumns j) =
          Pi.single j 1 := by
      intro j
      rw [← generatedAxisGlobalMaskColumnAction_decode, seventhForestXiPermInverse_certificate,
        generatedAxisGlobalMaskDecode_two_pow]
    have hPi : (co1BinaryAction (QuotientGroup.mk' signsSubgroup
        (golayPermutationIsometry generatedSeventhXiPlanePermutation)))⁻¹ v =
          generatedAxisGlobalMaskColumnMatrix seventhForestXiPermInverseColumns *ᵥ v := by
      change (co1BinaryAction _).symm v = _
      exact generatedAxisGlobalMaskColumnMatrix_inverse_apply _ _ _ hP hcol v
    have hXi : ∀ w, co1BinaryAction (QuotientGroup.mk' signsSubgroup co1XiIsometry) w =
        (leechHyperbolicInverse * co1XiBasisMatrix.map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) *ᵥ w := fun w => co1Xi_binaryAction w
    rw [seventhForestXiPlane_spatial]
    simp only [map_mul, map_inv, LinearEquiv.mul_apply]
    rw [hPi, hXi, hP, seventhForestXiPlaneColumns_certificate, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
