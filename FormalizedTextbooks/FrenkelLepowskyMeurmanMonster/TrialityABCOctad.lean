/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete triality covariance for the pair actions on signed-octad blocks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairFourier

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

theorem conwayShortPairing_pairOctad_local (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    conwayShortPairing (trialityPairMatrix (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (Sum.inr (Sum.inl (o,e))) = (trialityOctadPairSign a b e : ℝ) := by
  have hscale (x y : ℝ) : 2 * (x / Real.sqrt 8) * (y / Real.sqrt 8) = x * y / 4 := by
    have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hn : Real.sqrt 8 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
    nlinarith [congrArg (fun v : ℝ => x * y * v) hs]
  rw [trialityPairMatrix_short_pairing, griessPairIndex_coordinates]
  by_cases horder : golayOctadCoordinate o a < golayOctadCoordinate o b
  all_goals simp only [horder, ite_true, ite_false, griessShortVector]
  all_goals rw [hscale, griessOctad_integral_local, griessOctad_integral_local]
  all_goals cases ha : (trialityEvenMask e).testBit a.val
  all_goals cases hb : (trialityEvenMask e).testBit b.val
  all_goals norm_num [trialityOctadPairSign, ha, hb]

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_octad_zero (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 0
      (griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))))
      (griessConwayEncode (trialityOctadBasis o e)) =
      (trialityOctadPairSign a b e : ℝ) • griessConwayEncode (trialityOctadBasis o e) := by
  rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_octadBasis,
    trialityPairMatrix_raw_shortBasis, conwayShortPairing_pairOctad_local o a b e hab]

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_octad_one (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 1
      (griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))))
      (griessConwayEncode (trialityOctadBasis o e)) =
      -(trialityOctadPairSign a b e : ℝ) •
        griessConwayEncode (trialityOctadBasis o (trialityOctadPairFlip a b e)) := by
  have hactive := conwayRawProduct_pairOctad_active o a b e hab
  rw [griessConwayEncode_ABC_one_short, griessConwayEncode_octadBasis,
    griessConwayEncode_octadBasis, conwayRawProduct_sub_left]
  by_cases hc : trialityOctadPairColor a b e = 0
  · have hi := conwayRawProduct_pairOctad_inactive o a b e hab 1 (by rw [hc]; decide)
    rw [hc] at hactive
    rw [hactive, hi, sub_zero]
    have hsign : trialityOctadPairSign a b e = -1 := by
      cases ha : (trialityEvenMask e).testBit a.val <;>
        cases hb : (trialityEvenMask e).testBit b.val
      all_goals simp_all [trialityOctadPairColor, trialityOctadPairSign]
    rw [hsign]
    norm_num
  · have hc1 : trialityOctadPairColor a b e = 1 := by omega
    have hi := conwayRawProduct_pairOctad_inactive o a b e hab 0 (Ne.symm hc)
    rw [hc1] at hactive
    rw [hi, hactive, zero_sub]
    have hsign : trialityOctadPairSign a b e = 1 := by
      cases ha : (trialityEvenMask e).testBit a.val <;>
        cases hb : (trialityEvenMask e).testBit b.val
      all_goals simp_all [trialityOctadPairColor, trialityOctadPairSign]
    rw [hsign]
    norm_num

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_octad_two (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 2
      (griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))))
      (griessConwayEncode (trialityOctadBasis o e)) =
        griessConwayEncode (trialityOctadBasis o (trialityOctadPairFlip a b e)) := by
  have hactive := conwayRawProduct_pairOctad_active o a b e hab
  rw [griessConwayEncode_ABC_two_short, griessConwayEncode_octadBasis,
    griessConwayEncode_octadBasis, conwayRawProduct_add_left]
  by_cases hc : trialityOctadPairColor a b e = 0
  · have hi := conwayRawProduct_pairOctad_inactive o a b e hab 1 (by rw [hc]; decide)
    rw [hc] at hactive
    rw [hactive, hi, add_zero]
  · have hc1 : trialityOctadPairColor a b e = 1 := by omega
    have hi := conwayRawProduct_pairOctad_inactive o a b e hab 0 (Ne.symm hc)
    rw [hc1] at hactive
    rw [hi, hactive, zero_add]

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_octad_zero (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    griessProd (trialityABCBasis 0 (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (trialityOctadBasis o e) =
        (trialityOctadPairSign a b e : ℝ) • trialityOctadBasis o e :=
  griessProd_of_raw_smul _ _ _ _ (conwayRawProduct_ABC_octad_zero o a b e hab)

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_octad_one (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    griessProd (trialityABCBasis 1 (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (trialityOctadBasis o e) = -(trialityOctadPairSign a b e : ℝ) •
        trialityOctadBasis o (trialityOctadPairFlip a b e) :=
  griessProd_of_raw_smul _ _ _ _ (conwayRawProduct_ABC_octad_one o a b e hab)

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_octad_two (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    griessProd (trialityABCBasis 2 (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (trialityOctadBasis o e) = trialityOctadBasis o (trialityOctadPairFlip a b e) := by
  rw [griessProd_eq_conwayRawProduct, conwayRawProduct_ABC_octad_two o a b e hab,
    griessConwayDecode_encode]

theorem trialityOctadPairAReal_single (a b : Fin 8) (e : Fin 64) :
    (trialityOctadPairAReal a b).mulVec (Pi.single e 1) =
      (trialityOctadPairSign a b e : ℝ) • Pi.single e 1 := by
  ext f
  rw [trialityOctadPairAReal_mulVec]
  by_cases h : f = e <;> simp [h]

theorem trialityOctadPairBReal_single (a b : Fin 8) (e : Fin 64) :
    (trialityOctadPairBReal a b).mulVec (Pi.single e 1) =
      -(trialityOctadPairSign a b e : ℝ) • Pi.single (trialityOctadPairFlip a b e) 1 := by
  ext f
  simp [trialityOctadPairBReal, trialityOctadPairB, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem trialityOctadPairCReal_single (a b : Fin 8) (e : Fin 64) :
    (trialityOctadPairCReal a b).mulVec (Pi.single e 1) =
      (Pi.single (trialityOctadPairFlip a b e) 1 : Fin 64 → ℝ) := by
  ext f
  simp [trialityOctadPairCReal, trialityOctadPairC, Matrix.mulVec, dotProduct, Pi.single_apply]

@[simp] theorem trialityOctadIncl_apply (o : Fin 759) (v : Fin 64 → ℝ) :
    trialityOctadIncl o v = trialityOctadVector o v := rfl

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_octadVector_of_basis (x : GriessSpace) (o : Fin 759)
    (M : Matrix (Fin 64) (Fin 64) ℝ)
    (h : ∀ e : Fin 64, griessProd x (trialityOctadBasis o e) =
      trialityOctadVector o (M.mulVec (Pi.single e 1))) (v : Fin 64 → ℝ) :
    griessProd x (trialityOctadVector o v) = trialityOctadVector o (M.mulVec v) := by
  have hm : (griessProd x).comp (trialityOctadIncl o) =
      (trialityOctadIncl o).comp M.mulVecLin := by
    apply (Pi.basisFun ℝ (Fin 64)).ext
    intro e
    simpa only [Pi.basisFun_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      trialityOctadIncl_apply, trialityOctadBasis_eq_vector] using h e
  simpa only [LinearMap.comp_apply, trialityOctadIncl_apply, Matrix.mulVecLin_apply] using
    LinearMap.congr_fun hm v

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_octadVector_zero (o : Fin 759) (a b : Fin 8)
    (hab : a ≠ b) (v : Fin 64 → ℝ) :
    griessProd (trialityABCBasis 0 (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (trialityOctadVector o v) =
        trialityOctadVector o ((trialityOctadPairAReal a b).mulVec v) := by
  apply griessProd_octadVector_of_basis
  intro e
  rw [griessProd_ABC_octad_zero o a b e hab, trialityOctadPairAReal_single]
  exact (map_smul (trialityOctadIncl o) _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_octadVector_one (o : Fin 759) (a b : Fin 8)
    (hab : a ≠ b) (v : Fin 64 → ℝ) :
    griessProd (trialityABCBasis 1 (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (trialityOctadVector o v) =
        trialityOctadVector o ((trialityOctadPairBReal a b).mulVec v) := by
  apply griessProd_octadVector_of_basis
  intro e
  rw [griessProd_ABC_octad_one o a b e hab, trialityOctadPairBReal_single]
  exact (map_smul (trialityOctadIncl o) _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_octadVector_two (o : Fin 759) (a b : Fin 8)
    (hab : a ≠ b) (v : Fin 64 → ℝ) :
    griessProd (trialityABCBasis 2 (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (trialityOctadVector o v) =
        trialityOctadVector o ((trialityOctadPairCReal a b).mulVec v) := by
  apply griessProd_octadVector_of_basis
  intro e
  rw [griessProd_ABC_octad_two o a b e hab, trialityOctadPairCReal_single]
  rfl


/-- Actual Fourier triality intertwines all three pair actions on an arbitrary octad vector. -/
theorem sExtra_preserves_ABC_octadVector_local (o : Fin 759) (a b : Fin 8)
    (hab : a ≠ b) (s : Fin 3) (v : Fin 64 → ℝ) :
    sExtra (griessProd (trialityABCBasis s (griessPairIndex (golayOctadCoordinate o a)
      (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)))
      (trialityOctadVector o v)) =
      griessProd (sExtra (trialityABCBasis s (griessPairIndex (golayOctadCoordinate o a)
        (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab))))
        (sExtra (trialityOctadVector o v)) := by
  have h0 : trialityCycle (0 : Fin 3) = 1 := by decide +kernel
  have h1 : trialityCycle (1 : Fin 3) = 2 := by decide +kernel
  have h2 : trialityCycle (2 : Fin 3) = 0 := by decide +kernel
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl
  · rw [sExtra_ABC_basis, h0, sExtra_octadVector,
      griessProd_ABC_octadVector_zero o a b hab, sExtra_octadVector,
      griessProd_ABC_octadVector_one o a b hab, trialityOctadPair_action_AB a b hab]
  · rw [sExtra_ABC_basis, h1, sExtra_octadVector,
      griessProd_ABC_octadVector_one o a b hab, sExtra_octadVector,
      griessProd_ABC_octadVector_two o a b hab, trialityOctadPair_action_BC a b hab]
  · rw [sExtra_ABC_basis, h2, sExtra_octadVector,
      griessProd_ABC_octadVector_two o a b hab, sExtra_octadVector,
      griessProd_ABC_octadVector_zero o a b hab, trialityOctadPair_action_CA a b hab]

theorem conwayShortPairing_pairOctad_outside (p : Fin 276) (o : Fin 759) (e : Fin 64)
    (h : (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val ≠ true ∨
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val ≠ true) :
    conwayShortPairing (trialityPairMatrix p) (Sum.inr (Sum.inl (o,e))) = 0 := by
  rw [trialityPairMatrix_short_pairing]
  have hz (i : Fin 24) (hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true) :
      griessShortVector (Sum.inr (Sum.inl (o,e))) i = 0 := by
    rw [griessShortVector, griessOctad_integral_zero o e i hi]
    simp
  rcases h with h | h
  · rw [hz _ h, mul_zero, zero_mul]
  · rw [hz _ h, mul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_octad_outside (s : Fin 3) (p : Fin 276) (o : Fin 759) (e : Fin 64)
    (h : (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val ≠ true ∨
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val ≠ true) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis s p))
      (griessConwayEncode (trialityOctadBasis o e)) = 0 := by
  rw [griessConwayEncode_octadBasis]
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl
  · rw [griessConwayEncode_ABC_zero_sparse, trialityPairMatrix_raw_shortBasis,
      conwayShortPairing_pairOctad_outside p o e h, zero_smul]
  · rw [griessConwayEncode_ABC_one_short, conwayRawProduct_sub_left,
      conwayRawProduct_pairOctad_outside 0 p o e h,
      conwayRawProduct_pairOctad_outside 1 p o e h, sub_self]
  · rw [griessConwayEncode_ABC_two_short, conwayRawProduct_add_left,
      conwayRawProduct_pairOctad_outside 0 p o e h,
      conwayRawProduct_pairOctad_outside 1 p o e h, add_zero]

theorem griessProd_ABC_octad_outside (s : Fin 3) (p : Fin 276) (o : Fin 759) (e : Fin 64)
    (h : (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val ≠ true ∨
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val ≠ true) :
    griessProd (trialityABCBasis s p) (trialityOctadBasis o e) = 0 :=
  griessProd_of_raw_zero _ _ (conwayRawProduct_ABC_octad_outside s p o e h)

theorem griessProd_ABC_octadVector_outside (s : Fin 3) (p : Fin 276) (o : Fin 759)
    (v : Fin 64 → ℝ)
    (h : (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val ≠ true ∨
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val ≠ true) :
    griessProd (trialityABCBasis s p) (trialityOctadVector o v) = 0 := by
  rw [trialityOctadVector_sum, map_sum]
  simp only [map_smul, griessProd_ABC_octad_outside s p o _ h, smul_zero,
    Finset.sum_const_zero]

theorem griessPairIndex_congr {i j a b : Fin 24} (hij : i ≠ j) (hab : a ≠ b)
    (hi : i = a) (hj : j = b) : griessPairIndex i j hij = griessPairIndex a b hab := by
  subst a
  subst b
  rfl

/-- Triality preserves every product between an ABC pair and a signed octad. -/
theorem sExtra_preserves_ABC_octad_product (s : Fin 3) (p : Fin 276) (o : Fin 759) (e : Fin 64) :
    sExtra (griessProd (trialityABCBasis s p) (trialityOctadBasis o e)) =
      griessProd (sExtra (trialityABCBasis s p)) (sExtra (trialityOctadBasis o e)) := by
  rw [trialityOctadBasis_eq_vector]
  by_cases hi :
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val = true ∧
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val = true
  · obtain ⟨a, ha⟩ := golayOctadCoordinate_surjective o (griessCoordinatePair p).1 hi.1
    obtain ⟨b, hb⟩ := golayOctadCoordinate_surjective o (griessCoordinatePair p).2 hi.2
    have hab : a ≠ b := by
      intro h
      subst b
      exact griessCoordinatePair_ne p (ha.symm.trans hb)
    have hp : p = griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab) := by
      exact (griessPairIndex_pair p).symm.trans
        (griessPairIndex_congr (griessCoordinatePair_ne p)
          ((golayOctadCoordinate_injective o).ne hab) ha.symm hb.symm)
    rw [hp]
    exact sExtra_preserves_ABC_octadVector_local o a b hab s (Pi.single e 1)
  · have hout :
        (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val ≠ true ∨
        (golayEncodedMask (golayOctadLabel o).val).testBit
          (griessCoordinatePair p).2.val ≠ true := by
      by_cases hfirst :
          (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val = true
      · exact Or.inr (fun hsecond => hi ⟨hfirst, hsecond⟩)
      · exact Or.inl hfirst
    rw [sExtra_ABC_basis, sExtra_octadVector,
      griessProd_ABC_octadVector_outside s p o _ hout,
      griessProd_ABC_octadVector_outside (trialityCycle s) p o _ hout, map_zero]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
