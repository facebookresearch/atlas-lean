/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Reducing simplicity of the actual generated group to its local recognition inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.FusedInvolutionNormal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Recognition of the full centralizer turns the fused-involution intersection
into a nontrivial intersection with the actual embedded local subgroup. -/
theorem generated_normal_local_intersection_ne_bot_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    N.comap localIntoGenerated ≠ ⊥ := by
  intro h
  apply generated_normal_inf_centralizer_ne_bot N hN
  apply bot_unique
  rintro g ⟨hgN, hgC⟩
  obtain ⟨k, rfl⟩ := hC hgC
  have hk : k ∈ N.comap localIntoGenerated := hgN
  rw [h] at hk
  rw [Subgroup.mem_bot.mp hk, map_one]
  exact Subgroup.one_mem _

/-- Every nontrivial normal subgroup contains actual Q once the full centralizer
is recognized; the Conway orbit-span input is proved by the finite certificate. -/
theorem generated_q_range_le_of_nontrivial_normal_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : qIntoGenerated.range ≤ N :=
  generated_q_range_le_of_nontrivial_local_intersection N
    (generated_normal_local_intersection_ne_bot_of_centralizer_le_local hC N hN)

/-- Such a normal subgroup also contains the actual triality generator. -/
theorem generated_extra_mem_of_nontrivial_normal_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : extraIntoGenerated ∈ N :=
  extraIntoGenerated_mem_of_q_range_le N
    (generated_q_range_le_of_nontrivial_normal_of_centralizer_le_local hC N hN)

/-- Actual Q containment and full projection exhaust the local intersection. -/
theorem generated_local_range_le_of_q_range_le_projection_eq_top
    (N : Subgroup G) (hQ : qIntoGenerated.range ≤ N)
    (hP : (N.comap localIntoGenerated).map projH = ⊤) : localIntoGenerated.range ≤ N := by
  rintro g ⟨h, rfl⟩
  have hh : projH h ∈ (N.comap localIntoGenerated).map projH := by
    rw [hP]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, he⟩ := hh
  have hd : k⁻¹ * h ∈ projH.ker := by
    change projH (k⁻¹ * h) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [← inclQ_range_eq_projH_ker] at hd
  obtain ⟨q, hq⟩ := hd
  have hqd : localIntoGenerated (k⁻¹ * h) ∈ N := by
    rw [← hq]
    exact hQ ⟨q, rfl⟩
  have hm := N.mul_mem hk hqd
  simpa only [← map_mul, mul_inv_cancel_left] using hm

/-- The actual local image and triality generate all of G by its original definition. -/
theorem generated_subgroup_eq_top_of_local_range_le_extra_mem
    (N : Subgroup G) (hH : localIntoGenerated.range ≤ N)
    (hτ : extraIntoGenerated ∈ N) : N = ⊤ := by
  have hG : G ≤ N.map G.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro g (⟨h, rfl⟩ | hg)
    · exact Subgroup.mem_map.mpr ⟨localIntoGenerated h, hH ⟨h, rfl⟩, rfl⟩
    · have hg : g = sExtra := Set.mem_singleton_iff.mp hg
      subst g
      exact Subgroup.mem_map.mpr ⟨extraIntoGenerated, hτ, rfl⟩
  apply top_unique
  intro g _
  obtain ⟨k, hk, he⟩ := hG g.property
  have hkg : k = g := Subtype.ext he
  rwa [hkg] at hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
