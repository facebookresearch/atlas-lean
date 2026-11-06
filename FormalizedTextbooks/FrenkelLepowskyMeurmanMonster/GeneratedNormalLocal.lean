/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The faithful binary Conway action forces local elements centralizing Q to
lie in Q. This discharges the local normal-intersection prerequisite without
assuming simplicity of Co1 or irreducibility of its binary representation.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalSubgroups
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- Conjugation in the actual fiber group agrees with its constructed spin action. -/
theorem localFiberIncl_conjugate (f : localFiberSubgroup) (q : Q) :
    localFiberIncl (spinConjugation f.val.1 q) = f * localFiberIncl q * f⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact spinConjugation_representation f.val.1 q
  · change (1 : leechIsomSubgroup) = f.val.2 * 1 * f.val.2⁻¹
    simp

/-- The canonical map to the genuine quotient local group. -/
noncomputable def localFiberIntoH : localFiberSubgroup →* H :=
  QuotientGroup.mk' localDiagonalSubgroup

/-- The local centralizer of embedded Q is contained in embedded Q. -/
theorem local_centralizer_q_le_q : Subgroup.centralizer (inclQ.range : Set H) ≤ inclQ.range := by
  intro h hh
  induction h using QuotientGroup.induction_on with
  | H f =>
    have hs : spinConjugation f.val.1 = 1 := by
      apply MulEquiv.ext
      intro q
      apply inclQ_injective
      have hc := Subgroup.mem_centralizer_iff.mp hh (inclQ q) ⟨q, rfl⟩
      have hconj : inclQ (spinConjugation f.val.1 q) =
          localFiberIntoH f * inclQ q * (localFiberIntoH f)⁻¹ := by
        change QuotientGroup.mk' localDiagonalSubgroup
          (localFiberIncl (spinConjugation f.val.1 q)) = _
        rw [localFiberIncl_conjugate, map_mul, map_mul, map_inv]
        rfl
      change inclQ q * localFiberIntoH f = localFiberIntoH f * inclQ q at hc
      rw [hconj, ← hc, mul_assoc, mul_inv_cancel, mul_one]
      rfl
    have hb : spinBinaryAction f.val.1 = 1 := by
      change qBinaryAction (spinConjugation f.val.1) = 1
      rw [hs, map_one]
    have he : f.val.2 ∈ signsSubgroup :=
      (leechBinaryAction_mem_kernel_iff_sign _).mp (f.property.symm.trans hb)
    rw [inclQ_range_eq_projH_ker]
    change QuotientGroup.mk f.val.2 = (1 : leechIsomSubgroup ⧸ signsSubgroup)
    exact (QuotientGroup.eq_one_iff _).mpr he

/-- A nontrivial normal subgroup of the actual local group meets its embedded Q nontrivially. -/
theorem local_normal_q_intersection_ne_bot (K : Subgroup H) [K.Normal] (hK : K ≠ ⊥) :
    K.comap inclQ ≠ ⊥ := by
  intro hi
  have hnormal : inclQ.range.Normal := by
    rw [inclQ_range_eq_projH_ker]
    infer_instance
  have hcomm : ⁅K, inclQ.range⁆ = ⊥ := by
    apply bot_unique
    intro h hh
    have hKmem : h ∈ K := (Subgroup.commutator_le_left K inclQ.range) hh
    obtain ⟨q, rfl⟩ := (Subgroup.commutator_le_right K inclQ.range) hh
    have hq : q ∈ K.comap inclQ := hKmem
    rw [hi, Subgroup.mem_bot] at hq
    rw [hq, map_one]
    exact Subgroup.one_mem _
  have hle : K ≤ inclQ.range := by
    apply le_trans _ local_centralizer_q_le_q
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  apply hK
  apply bot_unique
  intro h hh
  obtain ⟨q, rfl⟩ := hle hh
  have hq : q ∈ K.comap inclQ := hh
  rw [hi, Subgroup.mem_bot] at hq
  rw [hq, map_one]
  exact Subgroup.one_mem _

/-- Every nontrivial normal subgroup of H contains the genuine extraspecial central involution. -/
theorem local_normal_contains_central (K : Subgroup H) [K.Normal] (hK : K ≠ ⊥) :
    inclQ qCentralInvolution ∈ K :=
  qCentralInvolution_mem_of_normal_nontrivial (K.comap inclQ)
    (local_normal_q_intersection_ne_bot K hK)

/-- Nontrivial intersection with the genuine local group forces the central involution into N. -/
theorem generatedCentral_mem_of_nontrivial_local_intersection (N : Subgroup ↥G) [N.Normal]
    (hN : N.comap localIntoGenerated ≠ ⊥) : qIntoGenerated qCentralInvolution ∈ N :=
  local_normal_contains_central (N.comap localIntoGenerated) hN

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
