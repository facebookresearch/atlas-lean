/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingFrameProjectionCoordinates

/-! Original Golay source congruences quantize the genuine rooted-frame projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

private theorem binary_val_cases (b : ZMod 2) : b.val = 0 ∨ b.val = 1 := by
  fin_cases b <;> decide

private theorem selected_square_nonneg (c : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) :
    0 ≤ generatedFeasibleContainingSelectedSquare c u :=
  Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Int.natCast_nonneg ((c i).val)) (sq_nonneg (u i)))

private theorem selected_square_le_norm (c : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) :
    generatedFeasibleContainingSelectedSquare c u ≤ leechSquareSum u := by
  apply Finset.sum_le_sum
  intro i _
  rcases binary_val_cases (c i) with hi | hi
  · simp only [hi, Int.natCast_zero, zero_mul]
    exact sq_nonneg _
  · simp only [hi, Int.natCast_one, one_mul]
    exact le_rfl

-- These finite scalar checks retain every original residue and all 17 norm-bounded values.
set_option maxHeartbeats 1000000 in
-- The complete scalar certificate checks all 17 bounded values and both original code bits.
private theorem scalar_even_square (a : ℤ) (b : ZMod 2) (ha : -8 ≤ a ∧ a ≤ 8)
    (hr : (a : ZMod 4) = 2 * (b.val : ZMod 4)) :
    (a ^ 2 : ZMod 8) = 4 * (b.val : ZMod 8) := by
  have h : ∀ k : Fin 17, ∀ b : ZMod 2,
      (((k.val : ℤ) - 8 : ℤ) : ZMod 4) = 2 * (b.val : ZMod 4) →
        ((((k.val : ℤ) - 8 : ℤ) : ZMod 8) ^ 2) = 4 * (b.val : ZMod 8) := by
    decide +kernel
  let k : Fin 17 := ⟨(a + 8).toNat, by omega⟩
  have hk : (k.val : ℤ) - 8 = a := by dsimp [k]; omega
  have he := h k b
  rw [hk] at he
  exact he hr

set_option maxHeartbeats 1000000 in
-- The complete odd scalar certificate checks the same 34 original residue cases.
private theorem scalar_odd_square (a : ℤ) (b : ZMod 2) (ha : -8 ≤ a ∧ a ≤ 8)
    (hr : (a : ZMod 4) = 1 + 2 * (b.val : ZMod 4)) :
    (a ^ 2 : ZMod 8) = 1 := by
  have h : ∀ k : Fin 17, ∀ b : ZMod 2,
      (((k.val : ℤ) - 8 : ℤ) : ZMod 4) = 1 + 2 * (b.val : ZMod 4) →
        ((((k.val : ℤ) - 8 : ℤ) : ZMod 8) ^ 2) = 1 := by
    decide +kernel
  let k : Fin 17 := ⟨(a + 8).toNat, by omega⟩
  have hk : (k.val : ℤ) - 8 = a := by dsimp [k]; omega
  have he := h k b
  rw [hk] at he
  exact he hr

/-- Actual Golay orthogonality makes every octad-selected norm-eight square sum divisible by eight.
-/
theorem generatedFeasibleContaining_selected_square_eight (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i : Fin 24, (c i).val = 8)
    (u : leechIntegral) (hu : leechSquareSum u.val = 64) :
    (8 : ℤ) ∣ generatedFeasibleContainingSelectedSquare c u.val := by
  have hb (i : Fin 24) : -8 ≤ u.val i ∧ u.val i ≤ 8 := by
    have h := leechNormEight_natAbs_le u.val hu i
    omega
  obtain ⟨m, hm, d, hd, hr, _⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
  rcases hm with rfl | rfl
  · have hs (i : Fin 24) := scalar_even_square (u.val i) (d i) (hb i)
      (by simpa only [Int.cast_zero, zero_add] using hr i)
    have he : (generatedFeasibleContainingSelectedSquare c u.val : ZMod 8) =
        4 * ((∑ i : Fin 24, ((c i).val : ℤ) * ((d i).val : ℤ) : ℤ) : ZMod 8) := by
      simp only [generatedFeasibleContainingSelectedSquare, Int.cast_sum, Int.cast_mul,
        Int.cast_pow, Int.cast_natCast, hs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rcases golayCode_intersection_even d c hd hc with ⟨k, hk⟩
    rw [he, hk]
    push_cast
    ring_nf
    change (k : ZMod 8) * (8 : ZMod 8) = 0
    rw [show (8 : ZMod 8) = 0 from by decide, mul_zero]
  · have hs (i : Fin 24) := scalar_odd_square (u.val i) (d i) (hb i)
      (by simpa only [Int.cast_one] using hr i)
    have hw8 : (∑ i : Fin 24, ((c i).val : ZMod 8)) = 0 := by
      have h := congrArg (fun n : ℕ => (n : ZMod 8)) hw
      rw [Nat.cast_sum] at h
      exact h.trans (by decide)
    simp only [generatedFeasibleContainingSelectedSquare, Int.cast_sum, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, hs, mul_one]
    exact hw8

/-- Root incidence gives the genuine selected norm lower bound, with no catalogue count premise.
-/
theorem generatedFeasibleContaining_selected_square_lower (c : Fin 24 → ZMod 2)
    (hc0 : c 0 = 1) (hc1 : c 1 = 1) (u : Fin 24 → ℤ)
    (hr : u 0 - u 1 = 8 ∨ u 0 - u 1 = -8) :
    32 ≤ generatedFeasibleContainingSelectedSquare c u := by
  have hc0v : (c 0).val = 1 := by rw [hc0]; decide
  have hc1v : (c 1).val = 1 := by rw [hc1]; decide
  have hl : u 0 ^ 2 + u 1 ^ 2 ≤ generatedFeasibleContainingSelectedSquare c u := by
    calc
      _ = ∑ i : Fin 24, ((if i = 0 then u 0 ^ 2 else 0) +
          (if i = 1 then u 1 ^ 2 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h0 : i = 0
        · subst i
          norm_num [hc0v]
        · by_cases h1 : i = 1
          · subst i
            norm_num [hc1v]
          · simp only [h0, h1, ite_false, zero_add]
            exact mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)
  rcases hr with hr | hr <;> nlinarith [sq_nonneg (u 0 + u 1)]

private theorem complement_weight_nonneg (b : ZMod 2) : 0 ≤ 1 - (b.val : ℤ) := by
  rcases binary_val_cases b with hb | hb <;> simp [hb]

private theorem scalar_even_small (a : ℤ) (b : ZMod 2) (ha : a ^ 2 ≤ 8)
    (hr : (a : ZMod 4) = 2 * (b.val : ZMod 4)) : a ^ 2 = 4 * (b.val : ℤ) := by
  have hlo : -2 ≤ a := by nlinarith
  have hhi : a ≤ 2 := by nlinarith
  have h : ∀ k : Fin 5, ∀ b : ZMod 2,
      (((k.val : ℤ) - 2 : ℤ) : ZMod 4) = 2 * (b.val : ZMod 4) →
        ((k.val : ℤ) - 2) ^ 2 = 4 * (b.val : ℤ) := by decide +kernel
  let k : Fin 5 := ⟨(a + 2).toNat, by omega⟩
  have hk : (k.val : ℤ) - 2 = a := by dsimp [k]; omega
  have he := h k b
  rw [hk] at he
  exact he hr

private theorem scalar_odd_nonzero (a : ℤ) (b : ZMod 2)
    (hr : (a : ZMod 4) = 1 + 2 * (b.val : ZMod 4)) : a ≠ 0 := by
  have h : ∀ b : ZMod 2, (0 : ZMod 4) ≠ 1 + 2 * (b.val : ZMod 4) := by decide +kernel
  intro hz
  rw [hz, Int.cast_zero] at hr
  exact h b hr

private theorem binary_add_integer_weight (a b : ZMod 2) :
    ((a + b).val : ℤ) = (a.val : ℤ) + (b.val : ℤ) - 2 * (a.val : ℤ) * (b.val : ℤ) := by
  have h : ∀ a b : ZMod 2,
      ((a + b).val : ℤ) = (a.val : ℤ) + (b.val : ℤ) -
        2 * (a.val : ℤ) * (b.val : ℤ) := by decide +kernel
  exact h a b

private theorem code_integer_weight_cases (d : Fin 24 → ZMod 2) (hd : d ∈ golayCode) :
    (∑ i : Fin 24, ((d i).val : ℤ)) = 0 ∨
      (∑ i : Fin 24, ((d i).val : ℤ)) = 8 ∨
      (∑ i : Fin 24, ((d i).val : ℤ)) = 12 ∨
      (∑ i : Fin 24, ((d i).val : ℤ)) = 16 ∨
      (∑ i : Fin 24, ((d i).val : ℤ)) = 24 := by
  have hcast : (∑ i : Fin 24, ((d i).val : ℤ)) =
      ((∑ i : Fin 24, (d i).val : ℕ) : ℤ) := by simp only [Nat.cast_sum]
  rw [hcast]
  have hw := golayCode_weights d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw | hw | hw | hw <;> rw [hw] <;> decide

private theorem binary_add_sum_integer_weight (c d : Fin 24 → ZMod 2) :
    (∑ i : Fin 24, (((c + d) i).val : ℤ)) =
      (∑ i : Fin 24, ((c i).val : ℤ)) + (∑ i : Fin 24, ((d i).val : ℤ)) -
        2 * (∑ i : Fin 24, ((c i).val : ℤ) * ((d i).val : ℤ)) := by
  have hf : (∑ i : Fin 24, 2 * ((c i).val : ℤ) * ((d i).val : ℤ)) =
      2 * (∑ i : Fin 24, ((c i).val : ℤ) * ((d i).val : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Pi.add_apply, binary_add_integer_weight, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hf]

set_option maxHeartbeats 1000000 in
-- Both complete source parity branches carry the original finite coordinate sums and code weights.
/-- A norm-eight frame cannot have complementary octad square sum eight in the actual Leech code.
The even case would give two octads with six common coordinates; the odd case needs sixteen
nonzero complementary coordinates. -/
theorem generatedFeasibleContaining_selected_square_ne_fifty_six (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i : Fin 24, (c i).val = 8)
    (u : leechIntegral) (hu : leechSquareSum u.val = 64) :
    generatedFeasibleContainingSelectedSquare c u.val ≠ 56 := by
  intro hS
  let R : ℤ := ∑ i : Fin 24, (1 - ((c i).val : ℤ)) * u.val i ^ 2
  have hC : (∑ i : Fin 24, ((c i).val : ℤ)) = 8 := by exact_mod_cast hw
  have hRS : R + generatedFeasibleContainingSelectedSquare c u.val = 64 := by
    rw [← hu]
    unfold R generatedFeasibleContainingSelectedSquare leechSquareSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hR : R = 8 := by omega
  have hnn (i : Fin 24) : 0 ≤ (1 - ((c i).val : ℤ)) * u.val i ^ 2 :=
    mul_nonneg (complement_weight_nonneg _) (sq_nonneg _)
  obtain ⟨m, hm, d, hd, hr, _⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  rcases hm with rfl | rfl
  · let U : ℤ := ∑ i : Fin 24, ((c i).val : ℤ) * ((d i).val : ℤ)
    let T : ℤ := ∑ i : Fin 24, (1 - ((c i).val : ℤ)) * ((d i).val : ℤ)
    let D : ℤ := ∑ i : Fin 24, ((d i).val : ℤ)
    have hsmall (i : Fin 24) (hi : (c i).val = 0) :
        u.val i ^ 2 = 4 * ((d i).val : ℤ) := by
      have hb := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
      change (1 - ((c i).val : ℤ)) * u.val i ^ 2 ≤ R at hb
      rw [hi, hR] at hb
      norm_num only [Int.natCast_zero, sub_zero, one_mul] at hb
      exact scalar_even_small _ _ hb (by simpa only [Int.cast_zero, zero_add] using hr i)
    have hRT : R = 4 * T := by
      unfold R T
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rcases binary_val_cases (c i) with hi | hi
      · rw [hsmall i hi, hi]
        ring
      · rw [hi]
        norm_num
    have hT : T = 2 := by omega
    have hU0 : 0 ≤ U := Finset.sum_nonneg (fun i _ =>
      mul_nonneg (Int.natCast_nonneg ((c i).val)) (Int.natCast_nonneg ((d i).val)))
    have hU8 : U ≤ 8 := by
      rw [← hC]
      apply Finset.sum_le_sum
      intro i _
      rcases binary_val_cases (d i) with hi | hi
      · rw [hi]
        simp only [Int.natCast_zero, mul_zero]
        exact Int.natCast_nonneg _
      · rw [hi]
        simp only [Int.natCast_one, mul_one]
        exact le_rfl
    have hDUT : D = U + T := by
      unfold D U T
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hDcases : D = 0 ∨ D = 8 ∨ D = 12 ∨ D = 16 ∨ D = 24 :=
      code_integer_weight_cases d hd
    have hD : D = 8 := by omega
    have hU : U = 6 := by omega
    have hxor : (∑ i : Fin 24, (((c + d) i).val : ℤ)) = 4 := by
      rw [binary_add_sum_integer_weight]
      change (∑ i : Fin 24, ((c i).val : ℤ)) + D - 2 * U = 4
      rw [hC, hD, hU]
      norm_num
    have hweights := code_integer_weight_cases (c + d) (golayCode.add_mem hc hd)
    rw [hxor] at hweights
    simp at hweights
  · have hsq (i : Fin 24) : 1 ≤ u.val i ^ 2 := by
      have hn := scalar_odd_nonzero (u.val i) (d i)
        (by simpa only [Int.cast_one] using hr i)
      have he : u.val i ≤ -1 ∨ 1 ≤ u.val i := by omega
      rcases he with he | he <;> nlinarith
    have hR16 : 16 ≤ R := by
      calc
        16 = ∑ i : Fin 24, (1 - ((c i).val : ℤ)) := by
          rw [Finset.sum_sub_distrib, hC]
          norm_num
        _ ≤ R := by
          apply Finset.sum_le_sum
          intro i _
          exact le_mul_of_one_le_right (complement_weight_nonneg _) (hsq i)
    omega

/-- All actual rooted-octad projection square sums have the four genuine integral values. -/
theorem generatedFeasibleContaining_selected_square_cases (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i : Fin 24, (c i).val = 8)
    (hc0 : c 0 = 1) (hc1 : c 1 = 1) (u : leechIntegral)
    (hu : leechSquareSum u.val = 64)
    (hr : u.val 0 - u.val 1 = 8 ∨ u.val 0 - u.val 1 = -8) :
    generatedFeasibleContainingSelectedSquare c u.val = 32 ∨
      generatedFeasibleContainingSelectedSquare c u.val = 40 ∨
      generatedFeasibleContainingSelectedSquare c u.val = 48 ∨
      generatedFeasibleContainingSelectedSquare c u.val = 64 := by
  have hl := generatedFeasibleContaining_selected_square_lower c hc0 hc1 u.val hr
  have hh := selected_square_le_norm c u.val
  rw [hu] at hh
  rcases generatedFeasibleContaining_selected_square_eight c hc hw u hu with ⟨k, hk⟩
  have he := generatedFeasibleContaining_selected_square_ne_fifty_six c hc hw u hu
  omega

/-- The entire actual mate-zero containing remainder has exactly three possible source diagonals.
-/
theorem generatedFeasibleContaining_noncoordinate_diagonal_cases (x : GriessSpace)
    (hx : x ∈ generatedFeasibleContainingNoncoordinateAxes) :
    (griessConwayEncode x).1 0 0 = (1 / 2 : ℝ) ∨
      (griessConwayEncode x).1 0 0 = (5 / 8 : ℝ) ∨
      (griessConwayEncode x).1 0 0 = (3 / 4 : ℝ) := by
  obtain ⟨f, hxf, hf⟩ := generatedFeasibleContaining_source_frame_lift x hx.1
  let c := golayOctadWord generatedFeasibleContainingOctadPrototypeIndex
  let u := generatedFeasibleContainingPullbackFrame f.val.2
  have hu : leechSquareSum u.val = 64 := generatedFeasibleContainingPullbackFrame_norm _
  have hc0 : c 0 = 1 := generatedFeasibleContaining_source_word_first.1
  have hc1 : c 1 = 1 := generatedFeasibleContaining_source_word_first.2
  have hs := generatedFeasibleContaining_selected_square_cases c (golayOctadWord_mem_code _)
    (golayOctadWord_weight _) hc0 hc1 u hu
    (generatedFeasibleContainingPullbackFrame_first_difference _ hf)
  have hfull : generatedFeasibleContainingSelectedSquare c u.val ≠ 64 := by
    intro hS
    have hsupp := generatedFeasibleContaining_selected_square_full_supported c u hu hS
    have hm := generatedFeasibleContaining_frame_full_mate_nonzero f hf hsupp
    rw [← hxf] at hm
    exact hm hx.2
  have hP : (griessConwayEncode x).1 = conwayMatrixAction f.val.2
      (Matrix.diagonal (fun i : Fin 24 => ((c i).val : ℝ))) := by
    rw [hxf, generatedFeasibleContaining_full_fiber_matrix]
  have hdiag := generatedFeasibleContaining_projection_frame_diagonal f.val.2 c
  rw [← hP] at hdiag
  rcases hs with hs | hs | hs | hs
  · rw [hs] at hdiag
    norm_num at hdiag
    left
    linarith
  · rw [hs] at hdiag
    norm_num at hdiag
    right
    left
    linarith
  · rw [hs] at hdiag
    norm_num at hdiag
    right
    right
    linarith
  · exact False.elim (hfull hs)

/-- All genuine noncoordinate triality destinations have first coefficient zero, one eighth,
or one quarter. This does not assume transport into any final A class. -/
theorem generatedFeasibleContaining_noncoordinate_outgoing_first_cases (x : GriessSpace)
    (hx : x ∈ generatedFeasibleContainingNoncoordinateAxes) :
    (griessConwayEncode (sExtra x)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 ∨
      (griessConwayEncode (sExtra x)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = (1 / 8 : ℝ) ∨
      (griessConwayEncode (sExtra x)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = (1 / 4 : ℝ) := by
  have hf := generatedFeasibleContaining_noncoordinate_triality_first x hx
  have hr := generatedFeasibleContaining_first_diagonal_relation x hx.1
  rcases generatedFeasibleContaining_noncoordinate_diagonal_cases x hx with hd | hd | hd
  · left
    linarith
  · right
    left
    linarith
  · right
    right
    linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
