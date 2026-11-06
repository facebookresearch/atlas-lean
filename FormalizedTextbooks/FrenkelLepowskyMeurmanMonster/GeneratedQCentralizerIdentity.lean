/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalLocal

/-! An actual identity criterion using the faithful embedded Q action and one tensor vector. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual global centralizer of all embedded Q has only its two central elements. -/
theorem generated_commuting_all_q_eq_one_or_central (g : G)
    (hg : ∀ q : Q, Commute g (qIntoGenerated q)) :
    g = 1 ∨ g = qIntoGenerated qCentralInvolution := by
  have hz : g ∈ Subgroup.centralizer {qIntoGenerated qCentralInvolution} :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hg qCentralInvolution)
  rw [generatedCentralizer_eq_local_range] at hz
  obtain ⟨h, hh⟩ := hz
  have hc : h ∈ Subgroup.centralizer (inclQ.range : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, rfl⟩
    apply localIntoGenerated_injective
    rw [map_mul, map_mul]
    change qIntoGenerated q * localIntoGenerated h = localIntoGenerated h * qIntoGenerated q
    rw [hh]
    exact (hg q).symm
  obtain ⟨q, hq⟩ := local_centralizer_q_le_q hc
  have hcenter : q ∈ centerQ := by
    change q ∈ Subgroup.center Q
    rw [Subgroup.mem_center_iff]
    intro r
    apply inclQ_injective
    rw [map_mul, map_mul, hq]
    exact Subgroup.mem_centralizer_iff.mp hc (inclQ r) ⟨r, rfl⟩
  have hb : q.base = 1 := (q_mem_center_iff_base_eq_one q).mp hcenter
  have hqphase : q = qCentral (toAdd q.coeff) := by
    apply NormalizedCocycleExtension.Extension.ext
    · exact hb
    · rfl
  have hqg : qIntoGenerated q = g := by
    change localIntoGenerated (inclQ q) = g
    rw [hq, hh]
  rw [hqphase] at hqg
  generalize hδ : toAdd q.coeff = δ at hqg
  fin_cases δ
  · change qIntoGenerated (qCentral 0) = g at hqg
    rw [show qCentral 0 = 1 from rfl, map_one] at hqg
    exact Or.inl hqg.symm
  · exact Or.inr hqg.symm

/-- Commuting with actual Q and fixing one vector with nonzero tensor coordinate
forces the actual group element to be the identity. -/
theorem generated_commuting_all_q_identity_of_tensor_fixed (g : G)
    (hg : ∀ q : Q, Commute g (qIntoGenerated q)) (x : GriessSpace)
    (hx : g.val x = x) (ht : (griessConwayEncode x).2.2 ≠ 0) : g = 1 := by
  rcases generated_commuting_all_q_eq_one_or_central g hg with h | h
  · exact h
  · rw [h] at hx
    have hp : x ∈ generatedCentralPlus := (mem_generatedCentralPlus x).mpr hx
    exact False.elim (ht ((mem_generatedCentralPlus_iff_tensor_zero x).mp hp))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
