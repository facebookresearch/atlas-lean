/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Completion of the actual normal-generation argument after centralizer recognition. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationOrbitPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalReduction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The two actual permutation classes generate all Golay permutation classes. -/
theorem co1GolayPermutation_mem_of_generators (K : Subgroup Co1)
    (h : ∀ k : Fin 2, (QuotientGroup.mk (omegaOrbitPermutationIsometry k) : Co1) ∈ K)
    (p : golayAutomorphismSubgroup) :
    (QuotientGroup.mk (golayPermutationIsometry p) : Co1) ∈ K := by
  have hle : golayTwoGeneratorSubgroup ≤ K.comap co1GolayPermutationClassHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact h k
  rw [golayTwoGeneratorSubgroup_eq_top] at hle
  exact hle (Subgroup.mem_top p)

/-- A normal subgroup of the actual Conway quotient containing all codeword signs is all Co₁.
Both permutation generators follow from the checked sign word, and ξ follows from a reflection. -/
theorem co1_normal_eq_top_of_golaySigns (K : Subgroup Co1) [K.Normal]
    (hs : ∀ c : golayCode, (QuotientGroup.mk (golaySignIsometry c) : Co1) ∈ K) : K = ⊤ := by
  have hp (p : golayAutomorphismSubgroup) :
      (QuotientGroup.mk (golayPermutationIsometry p) : Co1) ∈ K :=
    co1GolayPermutation_mem_of_generators K
      (omegaOrbitPermutation_class_mem_of_sign_mem K (hs (sourceGeneratedSignCode 16))) p
  have hxi : co1XiClass ∈ K :=
    co1XiClass_mem_of_reflectionClass_mem K (hs co1ReflectionCode)
  have hle : leechConcreteGeneratorSubgroup ≤ K.comap (QuotientGroup.mk' signsSubgroup) := by
    apply (Subgroup.closure_le _).mpr
    rintro e ((⟨c, rfl⟩ | ⟨p, rfl⟩) | he)
    · exact hs c
    · exact hp p
    · have he' : e = co1XiIsometry := Set.mem_singleton_iff.mp he
      subst e
      exact hxi
  rw [leechConcreteGeneratorSubgroup_eq_top] at hle
  apply top_unique
  intro c _
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective c
  exact hle (Subgroup.mem_top e)

/-- The projected local intersection of a nontrivial normal subgroup is now fully generated.
Only the actual full-centralizer inclusion remains as a geometric input. -/
theorem generated_normal_projection_eq_top_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    (N.comap localIntoGenerated).map projH = ⊤ := by
  let := generatedNormal_localProjection_normal N
  apply co1_normal_eq_top_of_golaySigns
  exact golaySign_mem_normal_projection_of_centralizer_le_local hC N
    (generated_q_range_le_of_nontrivial_normal_of_centralizer_le_local hC N hN)

/-- Every nontrivial normal subgroup is all G after full-centralizer recognition.
All orbit-span, code-sign, Mathieu generation, and Co₀ generation inputs are proved. -/
theorem generated_normal_eq_top_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : N = ⊤ := by
  apply generated_subgroup_eq_top_of_local_range_le_extra_mem N
  · exact generated_local_range_le_of_q_range_le_projection_eq_top N
      (generated_q_range_le_of_nontrivial_normal_of_centralizer_le_local hC N hN)
      (generated_normal_projection_eq_top_of_centralizer_le_local hC N hN)
  · exact generated_extra_mem_of_nontrivial_normal_of_centralizer_le_local hC N hN

/-- Simplicity of the actual generated group reduced to full-centralizer recognition.
This helper keeps the outstanding geometric assertion explicit in its hypothesis. -/
theorem generated_simple_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range) :
    IsSimpleGroup G := by
  have : Nontrivial G := generated_group_nontrivial
  refine ⟨fun N hnormal => ?_⟩
  let := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · exact Or.inr (generated_normal_eq_top_of_centralizer_le_local hC N hN)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
