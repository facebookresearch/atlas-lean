/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OctadPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OctadSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationMonomialFamilies

/-! Genuine monomial transitivity on the neighboring octad short lines. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Root-paired octad coordinates have equal signs. -/
theorem leechRootedA2Octad_equal_root_coordinates (d : Fin 759) (e : Fin 64)
    (h : leechRootedA2NeighborPredicate (Sum.inr (Sum.inl (d, e)))) :
    griessShortIntegral (Sum.inr (Sum.inl (d, e))) 0 =
      griessShortIntegral (Sum.inr (Sum.inl (d, e))) 1 := by
  have hh := (leechRootedA2Octad_neighbor_iff d e).mp h
  have hc := leechRootedA2Octad_first_coordinates d hh.1.1 hh.1.2
  have hs0 := leechRootedA2Octad_sign_at_coordinate d e 0
  have hs1 := leechRootedA2Octad_sign_at_coordinate d e 1
  rw [hc.1] at hs0
  rw [hc.2] at hs1
  change (griessOctadSignMask d e).testBit 0 = (trialityEvenMask e).testBit 0 at hs0
  change (griessOctadSignMask d e).testBit 1 = (trialityEvenMask e).testBit 1 at hs1
  have hsign : (griessOctadSignMask d e).testBit 0 =
      (griessOctadSignMask d e).testBit 1 := hs0.trans (hh.2.trans hs1.symm)
  change (if (golayEncodedMask (golayOctadLabel d).val).testBit 0 = true then
      (if (griessOctadSignMask d e).testBit 0 = true then (-2 : ℤ) else 2) else 0) =
    (if (golayEncodedMask (golayOctadLabel d).val).testBit 1 = true then
      (if (griessOctadSignMask d e).testBit 1 = true then (-2 : ℤ) else 2) else 0)
  rw [hh.1.1, hh.1.2, hsign]

/-- Each neighboring octad line reaches the positive standard octad preserving the root line. -/
theorem leechRootedA2Octad_monomial_reduction (o : Fin 759) (t : Fin 64)
    (hr : leechRootedA2NeighborPredicate (Sum.inr (Sum.inl (o, t)))) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine e ∧
      (leechIntegralAction e (griessShortLatticeVector (Sum.inr (Sum.inl (o, t))))).val =
        leechRootedA2PositiveOctad := by
  let u := griessShortLatticeVector (Sum.inr (Sum.inl (o, t)))
  let code : golayCode :=
    ⟨golayEncoder (golayLabelCoefficients (golayOctadLabel o)), ⟨_, rfl⟩⟩
  have hcoord (i : Fin 24) : u.val i ^ 2 = 4 * (code.val i).val := by
    change griessShortIntegral (Sum.inr (Sum.inl (o, t))) i ^ 2 =
      4 * (golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i).val
    rw [golayLabelEncoder_match]
    unfold griessShortIntegral
    split_ifs <;> simp_all
  have hh := (leechRootedA2Octad_neighbor_iff o t).mp hr
  obtain ⟨p, hp0, hp1, hp⟩ :=
    leechRootedA2Octad_permutation_to_standard o hh.1.1 hh.1.2
  let v := leechIntegralAction (golayPermutationIsometry p) u
  have hv (i : Fin 24) : v.val i ^ 2 = 4 * (golayStandardOctad i).val := by
    have he := congrFun hp i
    change code.val (p.val.symm i) = golayStandardOctad i at he
    change (leechIntegralAction (golayPermutationIsometry p) u).val i ^ 2 = _
    rw [leechIntegralAction_golayPermutation]
    simpa only [golayIntegerPermute, he] using hcoord (p.val.symm i)
  have hfirst (j : Fin 8) : v.val (Fin.castAdd 16 j) = -2 ∨
      v.val (Fin.castAdd 16 j) = 2 := by
    have he : v.val (Fin.castAdd 16 j) ^ 2 = (2 : ℤ) ^ 2 := by
      simpa only [golayStandardOctad, Fin.val_castAdd, j.isLt, ite_true,
        show (1 : ZMod 2).val = 1 by decide, Nat.cast_one, mul_one,
        show (2 : ℤ) ^ 2 = 4 by decide] using hv (Fin.castAdd 16 j)
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp he).symm
  have hzero (i : Fin 24) (hi : 8 ≤ i.val) : v.val i = 0 := by
    have hh := hv i
    simp [golayStandardOctad, show ¬ i.val < 8 by omega] at hh
    nlinarith
  have hroot : v.val 0 = v.val 1 := by
    have he0 : p.val.symm 0 = 0 := by rw [p.val.symm_apply_eq]; exact hp0.symm
    have he1 : p.val.symm 1 = 1 := by rw [p.val.symm_apply_eq]; exact hp1.symm
    change (leechIntegralAction (golayPermutationIsometry p) u).val 0 =
      (leechIntegralAction (golayPermutationIsometry p) u).val 1
    rw [leechIntegralAction_golayPermutation]
    change u.val (p.val.symm 0) = u.val (p.val.symm 1)
    rw [he0, he1]
    exact leechRootedA2Octad_equal_root_coordinates o t hr
  obtain ⟨d, hdroot, hd⟩ := leechRootedA2_standard_octad_signs v hfirst hzero hroot
  refine ⟨golaySignIsometry d * golayPermutationIsometry p, ⟨d, p, rfl⟩,
    leechRootedA2PreservesRootLine_mul _ _ hdroot
      (Or.inl (leechRootedA2Root_permutation p hp0 hp1)), ?_⟩
  simpa only [map_mul, LinearEquiv.mul_apply] using hd

/-- Actual monomial isometries preserving the root line are transitive on neighboring octads. -/
theorem leechRootedA2Octad_monomial_transitive (o p : Fin 759) (s t : Fin 64)
    (ho : leechRootedA2NeighborPredicate (Sum.inr (Sum.inl (o, s))))
    (hp : leechRootedA2NeighborPredicate (Sum.inr (Sum.inl (p, t)))) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine e ∧
      griessShortPermutation e (Sum.inr (Sum.inl (o, s))) = Sum.inr (Sum.inl (p, t)) := by
  obtain ⟨a, ha, haroot, hav⟩ := leechRootedA2Octad_monomial_reduction o s ho
  obtain ⟨b, hb, hbroot, hbv⟩ := leechRootedA2Octad_monomial_reduction p t hp
  let e := b⁻¹ * a
  have he : e.val (griessShortVector (Sum.inr (Sum.inl (o, s)))) =
      griessShortVector (Sum.inr (Sum.inl (p, t))) := by
    have hv : leechIntegralAction a (griessShortLatticeVector (Sum.inr (Sum.inl (o, s)))) =
        leechIntegralAction b (griessShortLatticeVector (Sum.inr (Sum.inl (p, t)))) :=
      Subtype.ext (hav.trans hbv.symm)
    have hvec := congrArg (fun u : leechIntegral => leechCoordinateEmbedding u.val) hv
    rw [leechIntegralAction_embedding, leechIntegralAction_embedding] at hvec
    change a.val (griessShortVector (Sum.inr (Sum.inl (o, s)))) =
      b.val (griessShortVector (Sum.inr (Sum.inl (p, t)))) at hvec
    change b.val.symm (a.val (griessShortVector (Sum.inr (Sum.inl (o, s))))) = _
    rw [hvec, b.val.symm_apply_apply]
  refine ⟨e, golayMonomialSubgroup.mul_mem (golayMonomialSubgroup.inv_mem hb) ha,
    leechRootedA2PreservesRootLine_mul _ _ (leechRootedA2PreservesRootLine_inv b hbroot)
      haroot, ?_⟩
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e (Sum.inr (Sum.inl (o, s))) with h | h
  · exact Or.inl (h.symm.trans he)
  · exact Or.inr (by
      rw [he] at h
      have hn := congrArg Neg.neg h
      simpa only [neg_neg] using hn.symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
