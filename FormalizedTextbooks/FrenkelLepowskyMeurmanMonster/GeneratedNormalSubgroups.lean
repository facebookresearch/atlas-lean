/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Concrete normal-subgroup prerequisites for the simplicity milestone.
The extraspecial argument in Conway's Appendix 1 implies that a nontrivial
normal subgroup of Q contains its central involution. Here this is proved
from the coordinate model, then transported to the actual generated group.
No assertion that a normal subgroup of G meets Q is assumed or proved here.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralInvolution

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- The only nonidentity element of the concrete extraspecial center is its central involution. -/
theorem qCentralInvolution_eq_of_mem_center_ne_one (q : Q)
    (hq : q ∈ centerQ) (hne : q ≠ 1) : q = qCentralInvolution := by
  have hb := (q_mem_center_iff_base_eq_one q).mp hq
  have hv : (toAdd q.coeff).val < 2 := (toAdd q.coeff).val_lt
  have hc : toAdd q.coeff = 0 ∨ toAdd q.coeff = 1 := by
    have hc : (toAdd q.coeff).val = 0 ∨ (toAdd q.coeff).val = 1 := by omega
    rcases hc with hc | hc
    · exact Or.inl ((ZMod.val_injective 2) hc)
    · exact Or.inr ((ZMod.val_injective 2) hc)
  rcases hc with hc | hc
  · exact (hne (NormalizedCocycleExtension.Extension.ext hb (congrArg ofAdd hc))).elim
  · exact NormalizedCocycleExtension.Extension.ext hb (congrArg ofAdd hc)

/-- Every nontrivial normal subgroup of Q contains its central involution. -/
theorem qCentralInvolution_mem_of_normal_nontrivial (K : Subgroup Q) [K.Normal]
    (hK : K ≠ ⊥) : qCentralInvolution ∈ K := by
  obtain ⟨q, hq, hne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hK)
  have hne : q ≠ 1 := by simpa only [Subgroup.mem_bot] using hne
  by_cases hc : q ∈ centerQ
  · rw [← qCentralInvolution_eq_of_mem_center_ne_one q hc hne]
    exact hq
  · have hw : ∃ w : Q, w * q ≠ q * w := by
      by_contra hw
      apply hc
      exact Subgroup.mem_center_iff.mpr (by simpa only [not_exists, not_not] using hw)
    obtain ⟨w, hw⟩ := hw
    have hcommK : ⁅w, q⁆ ∈ K :=
      (Subgroup.commutator_le_right (⊤ : Subgroup Q) K)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hq)
    have hcommC : ⁅w, q⁆ ∈ centerQ := q_commutator_le_center
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have hcommNe : ⁅w, q⁆ ≠ 1 := by
      exact fun h => hw (commutatorElement_eq_one_iff_mul_comm.mp h)
    rw [← qCentralInvolution_eq_of_mem_center_ne_one ⁅w, q⁆ hcommC hcommNe]
    exact hcommK

/-- A nontrivial intersection with embedded Q contains the genuine central involution. -/
theorem generatedCentral_mem_of_nontrivial_q_intersection (N : Subgroup ↥G) [N.Normal]
    (hN : N.comap qIntoGenerated ≠ ⊥) : qIntoGenerated qCentralInvolution ∈ N :=
  qCentralInvolution_mem_of_normal_nontrivial (N.comap qIntoGenerated) hN

/-- The genuine triality generator regarded as an element of the generated group. -/
noncomputable def extraIntoGenerated : ↥G := ⟨sExtra, sExtra_mem_generated_G⟩

/-- The three genuine triality signs regarded as elements of the generated group. -/
noncomputable def centralSignIntoGenerated (k : Fin 3) : ↥G :=
  ⟨trialityCentralSign k, trialityCentralSign_mem_G k⟩

/-- A normal subgroup containing the genuine central involution contains all its triality signs. -/
theorem centralSigns_mem_of_generatedCentral_mem (N : Subgroup ↥G) [hN : N.Normal]
    (hz : qIntoGenerated qCentralInvolution ∈ N) (k : Fin 3) :
    centralSignIntoGenerated k ∈ N := by
  have h0 : centralSignIntoGenerated 0 = qIntoGenerated qCentralInvolution := by
    apply Subtype.ext
    exact localCentralGriess_eq_trialityCentralSign.symm
  have h1 : centralSignIntoGenerated 1 =
      extraIntoGenerated * qIntoGenerated qCentralInvolution * extraIntoGenerated⁻¹ := by
    apply Subtype.ext
    exact localCentralGriess_conjugate.symm
  have h2 : centralSignIntoGenerated 2 =
      extraIntoGenerated ^ 2 * qIntoGenerated qCentralInvolution * (extraIntoGenerated ^ 2)⁻¹ := by
    apply Subtype.ext
    exact localCentralGriess_conjugate_square.symm
  fin_cases k
  · change centralSignIntoGenerated 0 ∈ N
    rw [h0]; exact hz
  · change centralSignIntoGenerated 1 ∈ N
    rw [h1]; exact hN.conj_mem _ hz _
  · change centralSignIntoGenerated 2 ∈ N
    rw [h2]; exact hN.conj_mem _ hz _

/-- Every normal subgroup meeting embedded Q nontrivially contains the entire actual Klein four. -/
theorem centralSigns_mem_of_nontrivial_q_intersection (N : Subgroup ↥G) [N.Normal]
    (hN : N.comap qIntoGenerated ≠ ⊥) (k : Fin 3) : centralSignIntoGenerated k ∈ N :=
  centralSigns_mem_of_generatedCentral_mem N
    (generatedCentral_mem_of_nontrivial_q_intersection N hN) k

/-- The actual central involution lies in the derived subgroup of the generated group. -/
theorem generatedCentral_mem_commutator :
    qIntoGenerated qCentralInvolution ∈ commutator ↥G := by
  have hmap : (commutator Q).map qIntoGenerated ≤ commutator ↥G := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap (Subgroup.mem_map_of_mem qIntoGenerated qCentralInvolution_mem_commutator)

/-- All three concrete triality signs lie in the derived subgroup. -/
theorem centralSigns_mem_commutator (k : Fin 3) :
    centralSignIntoGenerated k ∈ commutator ↥G :=
  centralSigns_mem_of_generatedCentral_mem (commutator ↥G)
    generatedCentral_mem_commutator k

/-- The generated group has a nontrivial derived subgroup; perfectness is not asserted. -/
theorem generated_commutator_ne_bot : commutator ↥G ≠ ⊥ := by
  intro h
  have hz := generatedCentral_mem_commutator
  rw [h, Subgroup.mem_bot] at hz
  apply qCentralInvolution_ne_one
  apply qIntoGenerated_injective
  exact hz.trans qIntoGenerated.map_one.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
