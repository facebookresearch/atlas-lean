/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOutsidePairOctadOrbitProof
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayStandardOctadOutsideSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryContainingOctadSigns

/-! Actual signs and original-word transport normalize every outside-pair octad preferred line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original encoder label3 is an actual octad. -/
theorem generatedFeasibleOutsideOctad_prototype_mem : (3 : Fin 4096) ∈ golayOctads := by
  decide +kernel

/-- The original dictionary index of the octad occupying physical coordinates8 through15. -/
def generatedFeasibleOutsideOctadPrototypeIndex : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨3, generatedFeasibleOutsideOctad_prototype_mem⟩

/-- The actual outside prototype is bound to source encoder label3. -/
theorem generatedFeasibleOutsideOctadPrototypeIndex_label :
    golayOctadLabel generatedFeasibleOutsideOctadPrototypeIndex = 3 :=
  congrArg Subtype.val
    ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨3, generatedFeasibleOutsideOctad_prototype_mem⟩)

/-- The preferred label of the actual positive outside-pair octad prototype. -/
def generatedFeasibleOutsideOctadPrototypeLabel : GriessShortIndex :=
  Sum.inr (Sum.inl (generatedFeasibleOutsideOctadPrototypeIndex, 0))

private theorem zero_octad_sign_mask (o : Fin 759) : griessOctadSignMask o 0 = 0 := by
  have he : trialityEvenMask 0 = 0 := by decide +kernel
  unfold griessOctadSignMask
  rw [he]
  have hf (xs : List (Fin 8)) : xs.foldr (fun k m =>
      (if (0 : ℕ).testBit k.val then 2 ^ (golayOctadCoordinate o k).val else 0) ||| m) 0 = 0 := by
    induction xs with
    | nil => rfl
    | cons k xs _ih => simp [List.foldr_cons]
  exact hf _

/-- The preferred prototype is the original integral vector twice coordinates8 through15. -/
theorem generatedFeasibleOutsideOctadPrototype_integral (i : Fin 24) :
    griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel i =
      if 8 ≤ i.val ∧ i.val < 16 then 2 else 0 := by
  have hm : golayEncodedMask 3 = 65280 := by decide +kernel
  have hb : ∀ j : Fin 24, (65280 : ℕ).testBit j.val = decide (8 ≤ j.val ∧ j.val < 16) := by
    decide +kernel
  simp only [generatedFeasibleOutsideOctadPrototypeLabel, griessShortIntegral,
    generatedFeasibleOutsideOctadPrototypeIndex_label, zero_octad_sign_mask,
    Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
  change (if (golayEncodedMask 3).testBit i.val then (2 : ℤ) else 0) = _
  rw [hm, hb]
  simp

/-- The original outside prototype lies in the source-defined outside physical sector. -/
theorem generatedFeasibleOutsideOctadPrototypeLabel_mem :
    generatedFeasibleOutsideOctadPrototypeLabel ∈ generatedFeasibleSecondaryNonPairLabels 1 := by
  have ho : generatedFeasibleOutsideOctadPrototypeIndex ∈ generatedFeasibleOctadOutsideLabels := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [generatedFeasibleOutsideOctadPrototypeIndex_label]
    decide +kernel
  change _ ∈ (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadOutsideLabels).map _
  refine Finset.mem_map.mpr ⟨(generatedFeasibleOutsideOctadPrototypeIndex, 0), ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho, ?_⟩
  change griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 0 =
    griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 1
  rw [generatedFeasibleOutsideOctadPrototype_integral,
    generatedFeasibleOutsideOctadPrototype_integral]
  rfl

/-- Source encoder label3 has precisely its original eight outside support coordinates. -/
theorem generatedFeasibleOutsideOctadPrototype_code (i : Fin 24) :
    (golayOutsidePairOctadNodeCode 0).val i =
      if 8 ≤ i.val ∧ i.val < 16 then 1 else 0 := by
  change golayEncoder (golayLabelCoefficients 3) i = _
  revert i
  decide +kernel

/-- Every actual standard octad vector admits positive signs with equal bits at any two
prescribed outside coordinates. -/
theorem generatedFeasibleOutsideOctad_standard_positive_signs (u : leechIntegral)
    (hfirst : ∀ j : Fin 8, u.val (Fin.castAdd 16 j) = -2 ∨
      u.val (Fin.castAdd 16 j) = 2)
    (hzero : ∀ i : Fin 24, 8 ≤ i.val → u.val i = 0)
    (a b : Fin 24) (ha : 8 ≤ a.val) (hb : 8 ≤ b.val) (hab : a ≠ b) :
    ∃ d : golayCode, d.val a = d.val b ∧
      (leechIntegralAction (golaySignIsometry d) u).val =
        fun i : Fin 24 => if i.val < 8 then 2 else 0 := by
  let bits : Fin 8 → ZMod 2 := fun j => if u.val (Fin.castAdd 16 j) = -2 then 1 else 0
  have heven : ∑ j, bits j = 0 := leechShort_standard_octad_even u hfirst hzero
  obtain ⟨d, hd, hpair⟩ := golayStandardOctad_even_signs_equal_outside bits heven a b ha hb hab
  have hrow (j : Fin 8) :
      (if d.val (Fin.castAdd 16 j) = 0 then u.val (Fin.castAdd 16 j)
        else -u.val (Fin.castAdd 16 j)) = 2 := by
    rw [hd j]
    rcases hfirst j with h | h <;> simp [bits, h]
  refine ⟨d, hpair, ?_⟩
  rw [leechIntegralAction_golaySign]
  funext i
  by_cases hi : i.val < 8
  · let j : Fin 8 := ⟨i.val, hi⟩
    have hj : Fin.castAdd 16 j = i := Fin.ext rfl
    simpa only [golayIntegerSign, hi, ite_true, hj] using hrow j
  · simp [golayIntegerSign, hzero i (by omega), hi]

set_option maxHeartbeats 8000000 in
-- Bind two genuine permutation transports and the full original preferred-label dictionary.
/-- Every actual outside-pair preferred line has a genuine original monomial transport to
its positive prototype fixing the original first preferred root line. -/
theorem generatedFeasibleOutsideOctad_monomial (o : Fin 759) (t : Fin 64)
    (ho : o ∈ generatedFeasibleOctadOutsideLabels) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) ∧
      griessShortPermutation e (Sum.inr (Sum.inl (o, t))) =
        generatedFeasibleOutsideOctadPrototypeLabel := by
  let u := griessShortLatticeVector (Sum.inr (Sum.inl (o, t)))
  have hcoord (i : Fin 24) : u.val i ^ 2 = 4 * ((generatedFeasibleOctadCode o).val i).val := by
    change griessShortIntegral (Sum.inr (Sum.inl (o, t))) i ^ 2 =
      4 * (golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i).val
    rw [golayLabelEncoder_match]
    unfold griessShortIntegral
    split_ifs <;> simp_all
  have hd : golayOctadLabel o ∈ generatedFeasibleOctadsOutsideRootPair := by
    obtain ⟨_, ho⟩ := Finset.mem_filter.mp ho
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ho⟩
    have hm := (golayOctads.orderIsoOfFin golayOctads_card o).property
    exact (Finset.mem_filter.mp hm).2
  obtain ⟨p, hp0, hp1, hp⟩ := golayOutsidePairOctad_to_prototype (golayOctadLabel o) hd
  let v := leechIntegralAction (golayPermutationIsometry p) u
  have hv (i : Fin 24) : v.val i ^ 2 = 4 * ((golayOutsidePairOctadNodeCode 0).val i).val := by
    have he := congrFun hp i
    change (generatedFeasibleOctadCode o).val (p.val.symm i) =
      (golayOutsidePairOctadNodeCode 0).val i at he
    change (leechIntegralAction (golayPermutationIsometry p) u).val i ^ 2 = _
    rw [leechIntegralAction_golayPermutation]
    simpa only [golayIntegerPermute, he] using hcoord (p.val.symm i)
  obtain ⟨q, hq⟩ := golayOctad_to_standard (golayOutsidePairOctadNodeCode 0).val
    (golayOutsidePairOctadNodeCode 0).property (by
      change (∑ i : Fin 24, (golayEncoder (golayLabelCoefficients 3) i).val) = 8
      rw [← golayLabel_weight]
      decide +kernel)
  let w := leechIntegralAction (golayPermutationIsometry q) v
  have hw (i : Fin 24) : w.val i ^ 2 = 4 * (golayStandardOctad i).val := by
    have he := congrFun hq i
    change (golayOutsidePairOctadNodeCode 0).val (q.val.symm i) = golayStandardOctad i at he
    change (leechIntegralAction (golayPermutationIsometry q) v).val i ^ 2 = _
    rw [leechIntegralAction_golayPermutation]
    simpa only [golayIntegerPermute, he] using hv (q.val.symm i)
  have hfirst (j : Fin 8) : w.val (Fin.castAdd 16 j) = -2 ∨
      w.val (Fin.castAdd 16 j) = 2 := by
    have he : w.val (Fin.castAdd 16 j) ^ 2 = (2 : ℤ) ^ 2 := by
      simpa only [golayStandardOctad, Fin.val_castAdd, j.isLt, ite_true,
        show (1 : ZMod 2).val = 1 by decide, Nat.cast_one, mul_one,
        show (2 : ℤ) ^ 2 = 4 by decide] using hw (Fin.castAdd 16 j)
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp he).symm
  have hzero (i : Fin 24) (hi : 8 ≤ i.val) : w.val i = 0 := by
    have hh := hw i
    simp [golayStandardOctad, show ¬ i.val < 8 by omega] at hh
    nlinarith
  have houtside (i : Fin 24) (hi : i = 0 ∨ i = 1) : 8 ≤ (q.val i).val := by
    have he := congrFun hq (q.val i)
    change (golayOutsidePairOctadNodeCode 0).val (q.val.symm (q.val i)) =
      golayStandardOctad (q.val i) at he
    rw [q.val.symm_apply_apply, generatedFeasibleOutsideOctadPrototype_code] at he
    have hz : ¬(8 ≤ i.val ∧ i.val < 16) := by rcases hi with rfl | rfl <;> decide
    simp only [hz, ite_false, golayStandardOctad] at he
    by_contra h
    have hl : (q.val i).val < 8 := by omega
    simp [hl] at he
  obtain ⟨c, hcp, hc⟩ := generatedFeasibleOutsideOctad_standard_positive_signs w hfirst hzero
    (q.val 0) (q.val 1) (houtside 0 (Or.inl rfl)) (houtside 1 (Or.inr rfl))
    (q.val.injective.ne (by decide : (0 : Fin 24) ≠ 1))
  let d := golayCodePermutation q⁻¹ c
  have hdp : d.val 0 = d.val 1 := by
    change c.val (q.val 0) = c.val (q.val 1)
    exact hcp
  have hpos : (leechIntegralAction (golaySignIsometry d) v).val =
      griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel := by
    funext i
    have hh := congrFun hc (q.val i)
    rw [leechIntegralAction_golaySign, leechIntegralAction_golayPermutation] at hh
    change (if c.val (q.val i) = 0 then v.val (q.val.symm (q.val i))
      else -v.val (q.val.symm (q.val i))) = (if (q.val i).val < 8 then 2 else 0) at hh
    rw [q.val.symm_apply_apply] at hh
    rw [leechIntegralAction_golaySign, generatedFeasibleOutsideOctadPrototype_integral]
    change (if c.val (q.val i) = 0 then v.val i else -v.val i) = _
    rw [hh]
    have he := congrFun hq (q.val i)
    change (golayOutsidePairOctadNodeCode 0).val (q.val.symm (q.val i)) =
      golayStandardOctad (q.val i) at he
    rw [q.val.symm_apply_apply, generatedFeasibleOutsideOctadPrototype_code,
      golayStandardOctad] at he
    split_ifs at he ⊢ <;> simp_all
  let e := golaySignIsometry d * golayPermutationIsometry p
  have he : e ∈ golayMonomialSubgroup := ⟨d, p, rfl⟩
  have hplus : griessShortPermutation e leechRootedA2RootAddress = leechRootedA2RootAddress := by
    apply (leechRootedA2RootLineSubgroup_mem e).mpr
    exact leechRootedA2PreservesRootLine_mul _ _ (leechRootedA2Root_sign d hdp)
      (Or.inl (leechRootedA2Root_permutation p hp0 hp1))
  change griessShortPermutation e (Sum.inl (1, generatedFeasiblePhysicalRootPair)) =
    Sum.inl (1, generatedFeasiblePhysicalRootPair) at hplus
  refine ⟨e, he, (generatedFeasible_monomial_pair_fix_iff e he).mpr hplus, ?_⟩
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  left
  apply Subtype.ext
  rw [map_mul, LinearEquiv.mul_apply]
  exact hpos

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
