/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseLift

/-! Genuine monomial transitivity on the octad and odd short families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A common integral monomial target yields actual short-label transitivity. -/
theorem generatedAxis_monomial_common_target (r s : GriessShortIndex)
    (a b : leechIsomSubgroup) (ha : a ∈ golayMonomialSubgroup)
    (hb : b ∈ golayMonomialSubgroup)
    (hv : leechIntegralAction a (griessShortLatticeVector r) =
      leechIntegralAction b (griessShortLatticeVector s)) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧ griessShortPermutation e r = s := by
  have hvec : a.val (griessShortVector r) = b.val (griessShortVector s) := by
    have h := congrArg (fun u : leechIntegral => leechCoordinateEmbedding u.val) hv
    rw [leechIntegralAction_embedding, leechIntegralAction_embedding] at h
    exact h
  let e := b⁻¹ * a
  have he : e.val (griessShortVector r) = griessShortVector s := by
    change b.val.symm (a.val (griessShortVector r)) = _
    rw [hvec, b.val.symm_apply_apply]
  refine ⟨e, golayMonomialSubgroup.mul_mem (golayMonomialSubgroup.inv_mem hb) ha, ?_⟩
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e r with h | h
  · exact Or.inl (h.symm.trans he)
  · exact Or.inr (by
      rw [he] at h
      have hn := congrArg Neg.neg h
      simpa only [neg_neg] using hn.symm)

/-- Any coordinate can be moved to zero by an actual Golay permutation. -/
theorem generatedAxis_golay_point_to_zero (j : Fin 24) :
    ∃ p : golayAutomorphismSubgroup, p.val j = 0 := by
  let a : Fin 4 → Fin 24 := fun k => Equiv.swap (0 : Fin 24) j (Fin.castAdd 20 k)
  let b : Fin 4 → Fin 24 := fun k => Fin.castAdd 20 k
  have hb : Function.Injective b := by
    intro x y h
    exact Fin.ext (congrArg (fun i : Fin 24 => i.val) h)
  have ha : Function.Injective a := (Equiv.swap (0 : Fin 24) j).injective.comp hb
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive a b ha hb
  exact ⟨p, by simpa [a, b] using hp 0⟩

/-- Cancelling its actual Golay signs and moving its exceptional coordinate
reduces every odd-family short vector to the same integral target. -/
theorem generatedAxis_odd_monomial_reduction (d : Fin 2048) (j : Fin 24) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      (leechIntegralAction e (griessShortLatticeVector (Sum.inr (Sum.inr (d, j))))).val =
        (fun i : Fin 24 => if i = 0 then -3 else 1) := by
  let dl : Fin 4096 := ⟨d.val, by omega⟩
  let code : golayCode := ⟨golayEncoder (golayLabelCoefficients dl), ⟨_, rfl⟩⟩
  obtain ⟨p, hp⟩ := generatedAxis_golay_point_to_zero j
  let e := golayPermutationIsometry p * golaySignIsometry code
  have he : e ∈ golayMonomialSubgroup :=
    ⟨golayCodePermutation p code, p, golayPermutation_sign_commute p code⟩
  refine ⟨e, he, ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golayPermutation,
    leechIntegralAction_golaySign]
  funext i
  have hpi : p.val.symm i = j ↔ i = 0 := by
    rw [p.val.symm_apply_eq, hp]
  have hc := golayLabelEncoder_match dl (p.val.symm i)
  have hz : code.val (p.val.symm i) = 0 ↔
      (golayEncodedMask d.val).testBit (p.val.symm i).val = false := by
    change golayEncoder (golayLabelCoefficients dl) (p.val.symm i) = 0 ↔ _
    rw [← ZMod.val_eq_zero, hc]
    change (if (golayEncodedMask d.val).testBit (p.val.symm i).val then 1 else 0) = 0 ↔ _
    cases (golayEncodedMask d.val).testBit (p.val.symm i).val <;> decide
  simp only [golayIntegerPermute, golayIntegerSign, griessShortLatticeVector,
    griessShortIntegral, hz, hpi]
  cases (golayEncodedMask d.val).testBit (p.val.symm i).val <;>
    by_cases hi : i = 0 <;> simp [hi]

/-- Actual monomial isometries are transitive on all odd short labels. -/
theorem generatedAxis_odd_monomial_transitive
    (d e : Fin 2048) (i j : Fin 24) :
    ∃ a : leechIsomSubgroup, a ∈ golayMonomialSubgroup ∧
      griessShortPermutation a (Sum.inr (Sum.inr (d, i))) = Sum.inr (Sum.inr (e, j)) := by
  obtain ⟨a, ha, har⟩ := generatedAxis_odd_monomial_reduction d i
  obtain ⟨b, hb, hbs⟩ := generatedAxis_odd_monomial_reduction e j
  exact generatedAxis_monomial_common_target _ _ a b ha hb (Subtype.ext (har.trans hbs.symm))

/-- Every actual octad short vector is reduced to one fixed signed standard
octad by genuine Golay permutations and signs, without using ξ. -/
theorem generatedAxis_octad_monomial_reduction (o : Fin 759) (t : Fin 64) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      (leechIntegralAction e (griessShortLatticeVector (Sum.inr (Sum.inl (o, t))))).val =
        leechShortOctadTarget := by
  let u := griessShortLatticeVector (Sum.inr (Sum.inl (o, t)))
  let code : golayCode :=
    ⟨golayEncoder (golayLabelCoefficients (golayOctadLabel o)), ⟨_, rfl⟩⟩
  have hw : ∑ i, (code.val i).val = 8 := by
    have hpoint (i : Fin 24) := golayLabelEncoder_match (golayOctadLabel o) i
    change (∑ i, (golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i).val) = 8
    simp_rw [hpoint]
    exact (golayMaskSupport_card _).symm.trans (golayOctad_support_card o)
  have hcoord (i : Fin 24) : u.val i ^ 2 = 4 * (code.val i).val := by
    change griessShortIntegral (Sum.inr (Sum.inl (o, t))) i ^ 2 =
      4 * (golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i).val
    rw [golayLabelEncoder_match]
    unfold griessShortIntegral
    split_ifs <;> simp_all
  obtain ⟨p, hp⟩ := golayOctad_to_standard code.val code.property hw
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
  obtain ⟨d, hd⟩ := leechShort_standard_octad_signs v hfirst hzero
  refine ⟨golaySignIsometry d * golayPermutationIsometry p, ⟨d, p, rfl⟩, ?_⟩
  simpa only [map_mul, LinearEquiv.mul_apply] using hd

/-- Actual monomial isometries are transitive on all octad short labels. -/
theorem generatedAxis_octad_monomial_transitive
    (o p : Fin 759) (s t : Fin 64) :
    ∃ a : leechIsomSubgroup, a ∈ golayMonomialSubgroup ∧
      griessShortPermutation a (Sum.inr (Sum.inl (o, s))) = Sum.inr (Sum.inl (p, t)) := by
  obtain ⟨a, ha, har⟩ := generatedAxis_octad_monomial_reduction o s
  obtain ⟨b, hb, hbs⟩ := generatedAxis_octad_monomial_reduction p t
  exact generatedAxis_monomial_common_target _ _ a b ha hb (Subtype.ext (har.trans hbs.symm))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
