/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryContainingOctadSupport

/-! Genuine root-line-preserving signs for standard containing-pair octad vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Under an actual monomial isometry the two original pair root lines have equivalent
fixing conditions, because their original binary classes differ by the genuine frame class. -/
theorem generatedFeasible_monomial_pair_fix_iff (e : leechIsomSubgroup)
    (he : e ∈ golayMonomialSubgroup) :
    griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) ↔
      griessShortPermutation e (Sum.inl (1, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (1, generatedFeasiblePhysicalRootPair) := by
  have hframe : leechModTwoAction e (leechReduction (leechCoordinateFrameLattice 0)) =
      leechReduction (leechCoordinateFrameLattice 0) := by
    rw [← leechFrameClass_stabilizer_eq_monomial] at he
    exact he
  have hplus : griessShortClass (Sum.inl (1, generatedFeasiblePhysicalRootPair)) =
      leechReduction (leechCoordinateFrameLattice 0) +
        griessShortClass (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
    unfold griessShortClass
    rw [generatedFeasible_pair_mate_integral, map_sub, sub_eq_add_neg,
      ← map_neg, leechReduction_neg]
  have hmi : griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      leechCoordinateFrameLattice 0 -
        griessShortLatticeVector (Sum.inl (1, generatedFeasiblePhysicalRootPair)) := by
    rw [generatedFeasible_pair_mate_integral]
    abel
  have hminus : griessShortClass (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      leechReduction (leechCoordinateFrameLattice 0) +
        griessShortClass (Sum.inl (1, generatedFeasiblePhysicalRootPair)) := by
    unfold griessShortClass
    rw [hmi, map_sub, sub_eq_add_neg, ← map_neg, leechReduction_neg]
  constructor
  · intro hp
    have hm : leechModTwoAction e
        (griessShortClass (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortClass (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
      rw [← griessShortPermutation_class, hp]
    apply griessShortClass_injective
    rw [griessShortPermutation_class, hplus, map_add, hframe, hm]
  · intro hp
    have hm : leechModTwoAction e
        (griessShortClass (Sum.inl (1, generatedFeasiblePhysicalRootPair))) =
          griessShortClass (Sum.inl (1, generatedFeasiblePhysicalRootPair)) := by
      rw [← griessShortPermutation_class, hp]
    apply griessShortClass_injective
    rw [griessShortPermutation_class, hminus, map_add, hframe, hm]

/-- Every actual standard octad vector perpendicular to the first root admits a genuine
Golay sign sending it to the positive prototype and preserving the ordered pair root line. -/
theorem generatedFeasibleContainingOctad_positive_signs (u : leechIntegral)
    (hfirst : ∀ j : Fin 8, u.val (Fin.castAdd 16 j) = -2 ∨
      u.val (Fin.castAdd 16 j) = 2)
    (hzero : ∀ i : Fin 24, 8 ≤ i.val → u.val i = 0)
    (hroot : u.val 0 = u.val 1) :
    ∃ d : golayCode, d.val 0 = d.val 1 ∧
      (leechIntegralAction (golaySignIsometry d) u).val =
        fun i : Fin 24 => if i.val < 8 then 2 else 0 := by
  let b : Fin 8 → ZMod 2 := fun j => if u.val (Fin.castAdd 16 j) = -2 then 1 else 0
  have hb : ∑ j, b j = 0 := leechShort_standard_octad_even u hfirst hzero
  obtain ⟨d, hd⟩ := golayStandardOctad_even_signs b hb
  have hd0 := hd 0
  have hd1 := hd 1
  change d.val 0 = (if u.val 0 = -2 then (1 : ZMod 2) else 0) at hd0
  change d.val 1 = (if u.val 1 = -2 then (1 : ZMod 2) else 0) at hd1
  have hdp : d.val 0 = d.val 1 := by rw [hd0, hd1, hroot]
  have hrow (j : Fin 8) :
      (if d.val (Fin.castAdd 16 j) = 0 then u.val (Fin.castAdd 16 j)
        else -u.val (Fin.castAdd 16 j)) = 2 := by
    rw [hd j]
    rcases hfirst j with h | h <;> simp [b, h]
  refine ⟨d, hdp, ?_⟩
  rw [leechIntegralAction_golaySign]
  funext i
  by_cases hi : i.val < 8
  · let j : Fin 8 := ⟨i.val, hi⟩
    have hj : Fin.castAdd 16 j = i := Fin.ext rfl
    simpa only [golayIntegerSign, hi, ite_true, hj] using hrow j
  · simp [golayIntegerSign, hzero i (by omega), hi]

/-- Every actual signed containing-pair preferred line has a genuine monomial transport
to the prototype fixing the original first preferred root line. -/
theorem generatedFeasibleContainingOctad_monomial (o : Fin 759) (t : Fin 64)
    (ho : o ∈ generatedFeasibleOctadContainingLabels)
    (hr : griessShortIntegral (Sum.inr (Sum.inl (o, t))) 0 =
      griessShortIntegral (Sum.inr (Sum.inl (o, t))) 1) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) ∧
      griessShortPermutation e (Sum.inr (Sum.inl (o, t))) =
        generatedFeasibleContainingOctadPrototypeLabel := by
  let u := griessShortLatticeVector (Sum.inr (Sum.inl (o, t)))
  have hcoord (i : Fin 24) : u.val i ^ 2 = 4 * ((generatedFeasibleOctadCode o).val i).val := by
    change griessShortIntegral (Sum.inr (Sum.inl (o, t))) i ^ 2 =
      4 * (golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i).val
    rw [golayLabelEncoder_match]
    unfold griessShortIntegral
    split_ifs <;> simp_all
  obtain ⟨p, hp0, hp1, hp⟩ := generatedFeasibleContainingOctad_to_standard o ho
  let v := leechIntegralAction (golayPermutationIsometry p) u
  have hv (i : Fin 24) : v.val i ^ 2 = 4 * (golayStandardOctad i).val := by
    have he := congrFun hp i
    change (generatedFeasibleOctadCode o).val (p.val.symm i) = golayStandardOctad i at he
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
    have hs0 : p.val.symm 0 = 0 := p.val.symm_apply_eq.mpr hp0.symm
    have hs1 : p.val.symm 1 = 1 := p.val.symm_apply_eq.mpr hp1.symm
    change (leechIntegralAction (golayPermutationIsometry p) u).val 0 =
      (leechIntegralAction (golayPermutationIsometry p) u).val 1
    rw [leechIntegralAction_golayPermutation]
    simpa only [golayIntegerPermute, hs0, hs1, u, griessShortLatticeVector] using hr
  obtain ⟨d, hdp, hd⟩ := generatedFeasibleContainingOctad_positive_signs v hfirst hzero hroot
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
  exact hd.trans (by funext i; exact (generatedFeasibleContainingOctadPrototype_integral i).symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
