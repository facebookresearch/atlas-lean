/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Normal containment of the two actual Golay permutation generators. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationOrbitPermutationsData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual coordinate permutations projected to the actual Conway quotient. -/
noncomputable def co1GolayPermutationClassHom : golayAutomorphismSubgroup →* Co1 :=
  (QuotientGroup.mk' signsSubgroup).comp golayPermutationHom

/-- The certified pair-swap word and its genuine Golay permutation have the same class. -/
theorem co1PairSwapGolay_class :
    co1GolayPermutationClassHom co1PairSwapGolay =
      (QuotientGroup.mk co1PairSwapIsometry : Co1) := by
  change (QuotientGroup.mk (golayPermutationIsometry co1PairSwapGolay) : Co1) = _
  rw [co1PairSwapIsometry_eq_golayPermutation]

/-- Each finite factor is in every normal subgroup containing the actual pair swap. -/
theorem co1NormalOrbitFactor_class_mem (K : Subgroup Co1) [hK : K.Normal]
    (hp : (QuotientGroup.mk co1PairSwapIsometry : Co1) ∈ K) (k : Fin 10) :
    co1GolayPermutationClassHom (co1NormalOrbitFactor k) ∈ K := by
  rw [co1NormalOrbitFactor, map_mul, map_mul, map_inv, co1PairSwapGolay_class]
  exact hK.conj_mem _ hp _

/-- The two published actual permutation classes belong to every normal subgroup
containing the pair-swap class. This uses only the two explicit checked words. -/
theorem omegaOrbitPermutation_class_mem_of_pairSwap_mem (K : Subgroup Co1) [K.Normal]
    (hp : (QuotientGroup.mk co1PairSwapIsometry : Co1) ∈ K) (k : Fin 2) :
    (QuotientGroup.mk (omegaOrbitPermutationIsometry k) : Co1) ∈ K := by
  change co1GolayPermutationClassHom (omegaOrbitGolayPermutation k) ∈ K
  rw [← co1NormalOrbitGenerator_certificate k, map_list_prod]
  apply K.list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
  exact co1NormalOrbitFactor_class_mem K hp i

/-- A normal subgroup containing the actual source sign0x10 contains both actual
Golay coordinate permutations used in the Ω spanning certificate. -/
theorem omegaOrbitPermutation_class_mem_of_sign_mem (K : Subgroup Co1) [K.Normal]
    (hs : (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode 16)) : Co1) ∈ K)
    (k : Fin 2) : (QuotientGroup.mk (omegaOrbitPermutationIsometry k) : Co1) ∈ K :=
  omegaOrbitPermutation_class_mem_of_pairSwap_mem K (co1PairSwapClass_mem_of_signClass_mem K hs) k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
