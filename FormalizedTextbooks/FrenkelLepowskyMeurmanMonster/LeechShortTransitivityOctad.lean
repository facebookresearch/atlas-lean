/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadSigns

/-! Reduction of actual short octad vectors by Golay signs and the source ξ. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The two signed tetrads which ξ sends to a pair vector. -/
def leechShortOctadTarget : Fin 24 → ℤ := fun i =>
  if i.val < 8 then if i.val % 4 = 0 then 2 else -2 else 0

/-- Any zero coordinate forces the source common parity and height to be even. -/
theorem leechShort_height_of_zero (u : leechIntegral) (i : Fin 24) (hz : u.val i = 0) :
    8 ∣ ∑ j, u.val j := by
  obtain ⟨m, hm, c, _, hr, hs⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  have hm0 : m = 0 := by
    rcases hm with hm | hm
    · exact hm
    · have hh := hr i
      rw [hz, hm] at hh
      have hv : (c i).val = 0 ∨ (c i).val = 1 := by have h := ZMod.val_lt (c i); omega
      rcases hv with hv | hv
      · norm_num [hv] at hh
        exact False.elim ((by decide : (0 : ZMod 4) ≠ 1) hh)
      · norm_num [hv] at hh
        exact False.elim ((by decide : (0 : ZMod 4) ≠ 3) hh)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
  simpa [hm0] using hs

/-- The actual height congruence forces an even sign pattern on the standard octad. -/
theorem leechShort_standard_octad_even (u : leechIntegral)
    (hfirst : ∀ j : Fin 8, u.val (Fin.castAdd 16 j) = -2 ∨
      u.val (Fin.castAdd 16 j) = 2)
    (hzero : ∀ i : Fin 24, 8 ≤ i.val → u.val i = 0) :
    (∑ j : Fin 8, (if u.val (Fin.castAdd 16 j) = -2 then 1 else 0 : ZMod 2)) = 0 := by
  classical
  let b : Fin 8 → ZMod 2 := fun j => if u.val (Fin.castAdd 16 j) = -2 then 1 else 0
  have hpoint (j : Fin 8) : u.val (Fin.castAdd 16 j) = 2 - 4 * ((b j).val : ℤ) := by
    rcases hfirst j with h | h
    · simp only [b, h, ite_true, show (1 : ZMod 2).val = 1 by decide, Nat.cast_one]
      norm_num
    · simp only [b, h, show (2 : ℤ) ≠ -2 by decide, ite_false, ZMod.val_zero,
        Nat.cast_zero, mul_zero, sub_zero]
  have hsum : (∑ i : Fin 24, u.val i) = 16 - 4 * ∑ j : Fin 8, ((b j).val : ℤ) := by
    rw [Fin.sum_univ_add (a := 8) (b := 16)]
    have hz : ∀ j : Fin 16, u.val (Fin.natAdd 8 j) = 0 := fun j => hzero _ (by simp)
    simp_rw [hz, hpoint]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hd := leechShort_height_of_zero u 8 (hzero 8 (by decide))
  rw [hsum] at hd
  have hd2 : 2 ∣ ∑ j : Fin 8, ((b j).val : ℤ) := by
    obtain ⟨k, hk⟩ := hd
    exact ⟨2 - k, by omega⟩
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ j : Fin 8, ((b j).val : ℤ)) 2).mpr hd2
  simpa only [Int.cast_sum, Int.cast_natCast, ZMod.natCast_zmod_val] using he

/-- Even octad signs can be changed to the two prescribed signed tetrads. -/
theorem leechShort_standard_octad_signs (u : leechIntegral)
    (hfirst : ∀ j : Fin 8, u.val (Fin.castAdd 16 j) = -2 ∨
      u.val (Fin.castAdd 16 j) = 2)
    (hzero : ∀ i : Fin 24, 8 ≤ i.val → u.val i = 0) :
    ∃ d : golayCode, (leechIntegralAction (golaySignIsometry d) u).val =
      leechShortOctadTarget := by
  classical
  let b : Fin 8 → ZMod 2 := fun j => if u.val (Fin.castAdd 16 j) = -2 then 1 else 0
  let target : Fin 8 → ZMod 2 := ![0, 1, 1, 1, 0, 1, 1, 1]
  have hb : ∑ j, b j = 0 := leechShort_standard_octad_even u hfirst hzero
  have ht : ∑ j, target j = 0 := by decide +kernel
  obtain ⟨d, hd⟩ := golayStandardOctad_even_signs (b + target) (by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hb, ht, zero_add])
  have hrow (j : Fin 8) :
      (if d.val (Fin.castAdd 16 j) = 0 then u.val (Fin.castAdd 16 j)
        else -u.val (Fin.castAdd 16 j)) = leechShortOctadTarget (Fin.castAdd 16 j) := by
    rw [hd j]
    rcases hfirst j with h | h <;> fin_cases j <;>
      simp_all [b, target, leechShortOctadTarget,
        show (1 : ZMod 2) + 1 = 0 by decide]
  refine ⟨d, ?_⟩
  rw [leechIntegralAction_golaySign]
  funext i
  by_cases hi : i.val < 8
  · let j : Fin 8 := ⟨i.val, hi⟩
    have hj : Fin.castAdd 16 j = i := Fin.ext rfl
    simpa only [hj, golayIntegerSign] using hrow j
  · simp [golayIntegerSign, hzero i (by omega), leechShortOctadTarget, hi]

/-- The exact integer source numerator sends the two tetrads to a negative pair. -/
theorem leechShort_octad_xi_certificate :
    co1XiNumerator *ᵥ leechShortOctadTarget =
      (2 : ℕ) • (fun i : Fin 24 => if i = 0 ∨ i = 4 then (-4 : ℤ) else 0) := by
  decide +kernel

/-- Every actual norm-four octad is reduced to the positive pair by concrete generators. -/
theorem leechShort_octad_reduction (u : leechIntegral) (hs : leechSquareSum u.val = 32)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8)
    (hcoord : ∀ i, u.val i ^ 2 = 4 * (c i).val) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard c hc hw
  let v := leechIntegralAction (golayPermutationIsometry p) u
  have hv (i : Fin 24) : v.val i ^ 2 = 4 * (golayStandardOctad i).val := by
    have he := congrFun hp i
    change c (p.val.symm i) = golayStandardOctad i at he
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
  let w := leechIntegralAction (golaySignIsometry d) v
  let x := leechIntegralAction co1XiIsometry w
  have hx : x.val = fun i : Fin 24 => if i = 0 ∨ i = 4 then (-4 : ℤ) else 0 := by
    have hh := co1Xi_integral_double w
    rw [hd, leechShort_octad_xi_certificate] at hh
    funext i
    have he := congrFun hh i
    change 2 * x.val i = 2 * (if i = 0 ∨ i = 4 then (-4 : ℤ) else 0) at he
    omega
  have hxs : leechSquareSum x.val = 32 := by
    dsimp [x, w, v]
    rw [leechIntegralAction_squareSum, leechIntegralAction_squareSum,
      leechIntegralAction_squareSum, hs]
  obtain ⟨e, he, hpair⟩ := leechShort_pair_reduction x hxs 0 4 (by decide)
    (by simp [hx]) (by simp [hx])
  refine ⟨e * co1XiIsometry * golaySignIsometry d * golayPermutationIsometry p,
    leechConcreteGeneratorSubgroup.mul_mem
      (leechConcreteGeneratorSubgroup.mul_mem
        (leechConcreteGeneratorSubgroup.mul_mem he co1XiIsometry_mem_concrete)
        (golaySignIsometry_mem_concrete d)) (golayPermutationIsometry_mem_concrete p), ?_⟩
  simpa only [map_mul, LinearEquiv.mul_apply] using hpair

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
