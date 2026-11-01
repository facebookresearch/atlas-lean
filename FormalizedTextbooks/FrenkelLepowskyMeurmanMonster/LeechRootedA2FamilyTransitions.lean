/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2XiTransport

/-! Actual standard-root transitions connect the three original neighboring short families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A preferred pair coordinate has square0 or16. -/
theorem leechRootedA2_pair_square (s : Fin 2) (p : Fin 276) (i : Fin 24) :
    griessShortIntegral (Sum.inl (s, p)) i ^ 2 = 0 ∨
      griessShortIntegral (Sum.inl (s, p)) i ^ 2 = 16 := by
  have hn := griessCoordinatePair_ne p
  simp only [griessShortIntegral]
  split_ifs <;> simp_all

/-- A coordinate of square4 identifies the actual octad family. -/
theorem leechRootedA2_family_of_four (r : GriessShortIndex) (i : Fin 24)
    (h : griessShortIntegral r i ^ 2 = 4) : leechRootedA2NeighborFamily r = 1 := by
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · rcases leechRootedA2_pair_square s p i with hp | hp <;> omega
  · rfl
  · rw [griessOdd_coordinate_square] at h
    split_ifs at h <;> norm_num at h

/-- A coordinate of square9 identifies the actual odd family. -/
theorem leechRootedA2_family_of_nine (r : GriessShortIndex) (i : Fin 24)
    (h : griessShortIntegral r i ^ 2 = 9) : leechRootedA2NeighborFamily r = 2 := by
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · rcases leechRootedA2_pair_square s p i with hp | hp <;> omega
  · have hp := griessOctad_coordinate_square_le d e i
    omega
  · rfl

/-- The actual short action retains every coordinate square despite its preferred global sign. -/
theorem leechRootedA2_short_action_square (e : leechIsomSubgroup) (r : GriessShortIndex)
    (i : Fin 24) : griessShortIntegral (griessShortPermutation e r) i ^ 2 =
      (leechIntegralAction e (griessShortLatticeVector r)).val i ^ 2 := by
  rcases leechRootedA2_short_integral_image e r with h | h <;> rw [h]
  · rfl
  · simp only [Submodule.coe_neg, Pi.neg_apply, neg_sq, griessShortLatticeVector]

/-- Pulling back a short label through an actual root transporter preserves its root incidence. -/
theorem leechRootedA2_neighbor_pullback (b : leechIsomSubgroup) (u : leechIntegral)
    (hb : leechIntegralAction b leechRootedA2Root = u) (r : GriessShortIndex)
    (hr : leechIntegralPairing u.val (griessShortLatticeVector r).val ^ 2 = 256) :
    leechRootedA2NeighborPredicate (griessShortPermutation b⁻¹ r) := by
  apply (leechRootedA2_neighbor_pairing_iff _).mpr
  have hbi : leechIntegralAction b⁻¹ u = leechRootedA2Root := by
    rw [← hb, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hp := leechRootedA2_integral_pairing_action b⁻¹ u (griessShortLatticeVector r)
  rcases leechRootedA2_short_integral_image b⁻¹ r with hi | hi <;>
    rw [hbi, hi] at hp <;>
    simp only [Submodule.coe_neg, leechIntegralPairing, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib] at hp hr ⊢ <;>
    (have hs := congrArg (fun n : ℤ => n ^ 2) hp
     simpa only [neg_sq] using hs.trans hr)

/-- A literal Xi family transition transfers to the genuine standard-root stabilizer. -/
theorem leechRootedA2_family_transition (r : GriessShortIndex) (a c : Fin 3)
    (ha : leechRootedA2NeighborFamily r = a)
    (hc : leechRootedA2NeighborFamily (griessShortPermutation co1XiIsometry r) = c)
    (hr : leechIntegralPairing leechRootedA2XiRoot.val
      (griessShortLatticeVector r).val ^ 2 = 256) :
    ∃ s t : leechRootedA2NeighborAddress, ∃ e : leechIsomSubgroup,
      leechRootedA2PreservesRootLine e ∧ griessShortPermutation e s.val = t.val ∧
      leechRootedA2NeighborFamily s.val = a ∧ leechRootedA2NeighborFamily t.val = c := by
  obtain ⟨b, hb, hbroot⟩ := leechRootedA2XiTransport_exists
  let e := b⁻¹ * co1XiIsometry * b
  have heroot : leechRootedA2PreservesRootLine e :=
    Or.inl (leechRootedA2XiTransport_conjugate_fixes b hbroot)
  let s := griessShortPermutation b⁻¹ r
  have hs : leechRootedA2NeighborPredicate s := leechRootedA2_neighbor_pullback b _ hbroot r hr
  let t := griessShortPermutation e s
  have ht : leechRootedA2NeighborPredicate t := leechRootedA2_root_action_neighbor e heroot s hs
  have heq : t = griessShortPermutation b⁻¹ (griessShortPermutation co1XiIsometry r) := by
    simp only [t, e, s, map_mul, Equiv.Perm.mul_apply]
    have hi : griessShortPermutation b (griessShortPermutation b⁻¹ r) = r := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hi]
  refine ⟨⟨s, hs⟩, ⟨t, ht⟩, e, heroot, rfl, ?_, ?_⟩
  · exact (leechRootedA2_monomial_preserves_family b⁻¹
      (golayMonomialSubgroup.inv_mem hb) r).trans ha
  · change leechRootedA2NeighborFamily t = c
    rw [heq]
    exact (leechRootedA2_monomial_preserves_family b⁻¹
      (golayMonomialSubgroup.inv_mem hb) _).trans hc

/-- The original preferred pair label at physical coordinates1 and4. -/
noncomputable def leechRootedA2XiPairAddress : GriessShortIndex :=
  Sum.inl (1, griessCoordinatePairEquiv.symm ⟨(1, 4), by decide +kernel⟩)

/-- The actual preferred pair label has the source transition's literal coordinates. -/
theorem leechRootedA2XiPairAddress_integral :
    griessShortLatticeVector leechRootedA2XiPairAddress = leechRootedA2XiPair := by
  have hp : griessCoordinatePair
      (griessCoordinatePairEquiv.symm ⟨(1, 4), by decide +kernel⟩) = (1, 4) :=
    congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply _)
  apply Subtype.ext
  simp only [leechRootedA2XiPairAddress, griessShortLatticeVector, griessShortIntegral,
    hp, leechRootedA2XiPair]
  norm_num

/-- A genuine standard-root stabilizer joins the pair and octad neighboring families. -/
theorem leechRootedA2_pair_octad_transition :
    ∃ s t : leechRootedA2NeighborAddress, ∃ e : leechIsomSubgroup,
      leechRootedA2PreservesRootLine e ∧ griessShortPermutation e s.val = t.val ∧
      leechRootedA2NeighborFamily s.val = 0 ∧ leechRootedA2NeighborFamily t.val = 1 := by
  apply leechRootedA2_family_transition leechRootedA2XiPairAddress 0 1 rfl
  · apply leechRootedA2_family_of_four _ 0
    rw [leechRootedA2_short_action_square, leechRootedA2XiPairAddress_integral,
      leechRootedA2XiPair_image]
    decide +kernel
  · rw [leechRootedA2XiPairAddress_integral]
    decide +kernel

/-- A genuine standard-root stabilizer joins the octad and odd neighboring families. -/
theorem leechRootedA2_octad_odd_transition :
    ∃ s t : leechRootedA2NeighborAddress, ∃ e : leechIsomSubgroup,
      leechRootedA2PreservesRootLine e ∧ griessShortPermutation e s.val = t.val ∧
      leechRootedA2NeighborFamily s.val = 1 ∧ leechRootedA2NeighborFamily t.val = 2 := by
  apply leechRootedA2_family_transition
    (Sum.inr (Sum.inl (leechRootedA2XiOctadIndex, 4))) 1 2 rfl
  · apply leechRootedA2_family_of_nine _ 2
    rw [leechRootedA2_short_action_square]
    change (leechIntegralAction co1XiIsometry leechRootedA2XiOctad).val 2 ^ 2 = 9
    rw [leechRootedA2XiOctad_image]
    simp only [Submodule.coe_neg, Pi.neg_apply, neg_sq, griessShortLatticeVector]
    rw [griessOdd_coordinate_square]
    rfl
  · change leechIntegralPairing leechRootedA2XiRoot.val leechRootedA2XiOctad.val ^ 2 = 256
    rw [leechRootedA2XiOctad_coordinates]
    decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
