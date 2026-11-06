/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Triality preservation for all products in the three coordinate-pair blocks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityABCProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairEdgeQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairShortSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

theorem trialityPairMatrix_index (i j : Fin 24) (hij : i ≠ j) :
    trialityPairMatrix (griessPairIndex i j hij) =
      Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) +
        Matrix.vecMulVec (Pi.single j 1) (Pi.single i 1) := by
  simp only [trialityPairMatrix, griessPairIndex_coordinates]
  by_cases h : i < j
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    exact add_comm _ _

theorem trialityPairMatrix_index_mul_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    trialityPairMatrix (griessPairIndex i j hij) *
      trialityPairMatrix (griessPairIndex j k hjk) =
        Matrix.vecMulVec (Pi.single i 1) (Pi.single k 1) := by
  rw [trialityPairMatrix_index, trialityPairMatrix_index]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
    single_dotProduct, one_mul, Pi.single_apply, ite_true,
    ite_eq_right hij, ite_eq_right hjk, ite_eq_right hik, zero_smul, one_smul,
    Matrix.vecMulVec_zero, add_zero]

theorem conwayRawProduct_pureMatrix (M N : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayRawProduct (M, (0, 0)) (N, (0, 0)) = ((2 : ℝ) • (M * N + N * M), (0, 0)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero,
      add_zero, ite_self, Finset.sum_const_zero, zero_div, Matrix.smul_apply,
      Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib, smul_eq_mul]
  · funext u
    simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
      ite_self, Finset.sum_const_zero, zero_div]
  · funext t i
    simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
      Finset.sum_const_zero, zero_div]

theorem conwayRawProduct_ABC_zero_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 0 (griessPairIndex i j hij)))
      (griessConwayEncode (trialityABCBasis 0 (griessPairIndex j k hjk))) =
        (2 : ℝ) • griessConwayEncode (trialityABCBasis 0 (griessPairIndex i k hik)) := by
  rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_zero_sparse,
    griessConwayEncode_ABC_zero_sparse, conwayRawProduct_pureMatrix,
    trialityPairMatrix_index_mul_triangle i j k hij hjk hik]
  have hr := trialityPairMatrix_index_mul_triangle k j i hjk.symm hij.symm hik.symm
  rw [griessPairIndex_swap k j hjk.symm, griessPairIndex_swap j i hij.symm] at hr
  rw [hr, trialityPairMatrix_index]
  refine Prod.ext rfl ?_
  simp

theorem griessPairIndex_triangle_ne (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    griessPairIndex i j hij ≠ griessPairIndex j k hjk := by
  intro h
  have he := congrArg griessPairIncidence h
  rw [griessPairIncidence_index, griessPairIncidence_index] at he
  have hsingle : (Pi.single i 1 : Fin 24 → ZMod 2) = Pi.single k 1 := by
    exact add_right_cancel (by calc
      _ = Pi.single j 1 + Pi.single k 1 := he
      _ = Pi.single k 1 + Pi.single j 1 := add_comm _ _)
  have hv := congrFun hsingle i
  simp [hik] at hv

theorem conwayRawProduct_ABC_one_of_incidence (p q r : Fin 276)
    (hpq : p ≠ q)
    (hinc : griessPairIncidence p + griessPairIncidence q = griessPairIncidence r) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 1 p))
      (griessConwayEncode (trialityABCBasis 1 q)) =
        (2 : ℝ) • griessConwayEncode (trialityABCBasis 1 r) := by
  have h00 := conwayRawProduct_pairBasis_of_incidence 0 0 0 p q r hpq (by decide) hinc
  have h01 := conwayRawProduct_pairBasis_of_incidence 0 1 1 p q r hpq (by decide) hinc
  have h10 := conwayRawProduct_pairBasis_of_incidence 1 0 1 p q r hpq (by decide) hinc
  have h11 := conwayRawProduct_pairBasis_of_incidence 1 1 0 p q r hpq (by decide) hinc
  rw [griessConwayEncode_ABC_one_short, griessConwayEncode_ABC_one_short,
    griessConwayEncode_ABC_one_short, conwayRawProduct_sub_left, conwayRawProduct_sub_right,
    conwayRawProduct_sub_right, h00, h01, h10, h11]
  module

theorem conwayRawProduct_ABC_two_of_incidence (p q r : Fin 276)
    (hpq : p ≠ q)
    (hinc : griessPairIncidence p + griessPairIncidence q = griessPairIncidence r) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 2 p))
      (griessConwayEncode (trialityABCBasis 2 q)) =
        (2 : ℝ) • griessConwayEncode (trialityABCBasis 2 r) := by
  have h00 := conwayRawProduct_pairBasis_of_incidence 0 0 0 p q r hpq (by decide) hinc
  have h01 := conwayRawProduct_pairBasis_of_incidence 0 1 1 p q r hpq (by decide) hinc
  have h10 := conwayRawProduct_pairBasis_of_incidence 1 0 1 p q r hpq (by decide) hinc
  have h11 := conwayRawProduct_pairBasis_of_incidence 1 1 0 p q r hpq (by decide) hinc
  rw [griessConwayEncode_ABC_two_short, griessConwayEncode_ABC_two_short,
    griessConwayEncode_ABC_two_short, conwayRawProduct_add_left, conwayRawProduct_add_right,
    conwayRawProduct_add_right, h00, h01, h10, h11]
  module

theorem conwayRawProduct_ABC_one_two_of_incidence (p q r : Fin 276)
    (hpq : p ≠ q)
    (hinc : griessPairIncidence p + griessPairIncidence q = griessPairIncidence r) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 1 p))
      (griessConwayEncode (trialityABCBasis 2 q)) = 0 := by
  have h00 := conwayRawProduct_pairBasis_of_incidence 0 0 0 p q r hpq (by decide) hinc
  have h01 := conwayRawProduct_pairBasis_of_incidence 0 1 1 p q r hpq (by decide) hinc
  have h10 := conwayRawProduct_pairBasis_of_incidence 1 0 1 p q r hpq (by decide) hinc
  have h11 := conwayRawProduct_pairBasis_of_incidence 1 1 0 p q r hpq (by decide) hinc
  rw [griessConwayEncode_ABC_one_short, griessConwayEncode_ABC_two_short,
    conwayRawProduct_sub_left, conwayRawProduct_add_right, conwayRawProduct_add_right,
    h00, h01, h10, h11]
  exact sub_eq_zero.mpr (add_comm _ _)

theorem trialityPairMatrix_raw_shortBasis (p : Fin 276) (r : GriessShortIndex) :
    conwayRawProduct (trialityPairMatrix p, (0, 0)) (conwayShortBasis r) =
      conwayShortPairing (trialityPairMatrix p) r • conwayShortBasis r := by
  rw [conwayShortBasis, trialityPairMatrix_raw_restriction, trialityPairMatrix_short_pairing]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · simp
  · funext u
    by_cases hu : u = r
    · subst u
      simp
    · simp [hu]
  · funext t i
    simp

theorem griessPairVector_index_off_support (s : Fin 2) (j k : Fin 24) (hjk : j ≠ k)
    (i : Fin 24) (hij : i ≠ j) (hik : i ≠ k) :
    griessShortVector (Sum.inl (s, griessPairIndex j k hjk)) i = 0 := by
  rw [griessShortVector]
  have ha : i ≠ (griessCoordinatePair (griessPairIndex j k hjk)).1 := by
    rw [griessPairIndex_coordinates]
    by_cases h : j < k <;> simp [h, hij, hik]
  have hb : i ≠ (griessCoordinatePair (griessPairIndex j k hjk)).2 := by
    rw [griessPairIndex_coordinates]
    by_cases h : j < k <;> simp [h, hij, hik]
  rw [griessPairIntegral_off_support s _ i ha hb]
  simp

theorem conwayShortPairing_pair_triangle (s : Fin 2) (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    conwayShortPairing (trialityPairMatrix (griessPairIndex i j hij))
      (Sum.inl (s, griessPairIndex j k hjk)) = 0 := by
  rw [trialityPairMatrix_short_pairing, griessPairIndex_coordinates]
  by_cases h : i < j <;>
    simp [h, griessPairVector_index_off_support s j k hjk i hij hik]

theorem conwayRawProduct_pair_short_triangle (s : Fin 2) (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    conwayRawProduct (trialityPairMatrix (griessPairIndex i j hij), (0, 0))
      (conwayShortBasis (Sum.inl (s, griessPairIndex j k hjk))) = 0 := by
  rw [trialityPairMatrix_raw_shortBasis,
    conwayShortPairing_pair_triangle s i j k hij hjk hik, zero_smul]

theorem conwayRawProduct_ABC_zero_one_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 0 (griessPairIndex i j hij)))
      (griessConwayEncode (trialityABCBasis 1 (griessPairIndex j k hjk))) = 0 := by
  rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_one_short,
    conwayRawProduct_sub_right, conwayRawProduct_pair_short_triangle 0 i j k hij hjk hik,
    conwayRawProduct_pair_short_triangle 1 i j k hij hjk hik, sub_self]

theorem conwayRawProduct_ABC_zero_two_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 0 (griessPairIndex i j hij)))
      (griessConwayEncode (trialityABCBasis 2 (griessPairIndex j k hjk))) = 0 := by
  rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_two_short,
    conwayRawProduct_add_right, conwayRawProduct_pair_short_triangle 0 i j k hij hjk hik,
    conwayRawProduct_pair_short_triangle 1 i j k hij hjk hik, add_zero]

theorem trialityPairMatrix_mul_disjoint (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2) :
    trialityPairMatrix p * trialityPairMatrix q = 0 := by
  simp only [trialityPairMatrix, Matrix.add_mul, Matrix.mul_add,
    Matrix.vecMulVec_mul_vecMulVec, single_dotProduct, one_mul, Pi.single_apply,
    ite_eq_right h11, ite_eq_right h12, ite_eq_right h21, ite_eq_right h22,
    zero_smul, Matrix.vecMulVec_zero, add_zero]

theorem conwayRawProduct_ABC_zero_disjoint (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 0 p))
      (griessConwayEncode (trialityABCBasis 0 q)) = 0 := by
  rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_zero_sparse,
    conwayRawProduct_pureMatrix, trialityPairMatrix_mul_disjoint p q h11 h12 h21 h22,
    trialityPairMatrix_mul_disjoint q p h11.symm h21.symm h12.symm h22.symm,
    add_zero, smul_zero]
  rfl

theorem pairIndex_edges_cases (a b c d : Fin 24) (hab : a ≠ b) (hcd : c ≠ d)
    (hpq : griessPairIndex a b hab ≠ griessPairIndex c d hcd) :
    (∃ i j k : Fin 24, ∃ hij : i ≠ j, ∃ hjk : j ≠ k, ∃ _hik : i ≠ k,
      griessPairIndex a b hab = griessPairIndex i j hij ∧
        griessPairIndex c d hcd = griessPairIndex j k hjk) ∨
      (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) := by
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := by intro h; subst d; exact hpq rfl
    exact Or.inl ⟨b, a, d, hab.symm, hcd, hbd, griessPairIndex_swap a b hab, rfl⟩
  · by_cases had : a = d
    · subst d
      have hbc : b ≠ c := by
        intro h
        subst c
        exact hpq (griessPairIndex_swap a b hab)
      exact Or.inl ⟨b, a, c, hab.symm, hcd.symm, hbc,
        griessPairIndex_swap a b hab, griessPairIndex_swap c a hcd⟩
    · by_cases hbc : b = c
      · subst c
        have had' : a ≠ d := by
          intro h
          subst d
          exact hpq (griessPairIndex_swap a b hab)
        exact Or.inl ⟨a, b, d, hab, hcd, had', rfl, rfl⟩
      · by_cases hbd : b = d
        · subst d
          have hac' : a ≠ c := by intro h; subst c; exact hpq rfl
          exact Or.inl ⟨a, b, c, hab, hcd.symm, hac', rfl, griessPairIndex_swap c b hcd⟩
        · exact Or.inr ⟨hac, had, hbc, hbd⟩

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_of_raw_smul (x y z : GriessSpace) (c : ℝ)
    (h : conwayRawProduct (griessConwayEncode x) (griessConwayEncode y) =
      c • griessConwayEncode z) : griessProd x y = c • z := by
  rw [griessProd_eq_conwayRawProduct, h]
  change griessConwayDecodeLinear (c • griessConwayEncode z) = _
  rw [map_smul]
  exact congrArg (fun v : GriessSpace => c • v) (griessConwayDecode_encode z)

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_of_raw_zero (x y : GriessSpace)
    (h : conwayRawProduct (griessConwayEncode x) (griessConwayEncode y) = 0) :
    griessProd x y = 0 := by
  rw [griessProd_eq_conwayRawProduct, h]
  exact map_zero griessConwayDecodeLinear

theorem griessProd_ABC_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t : Fin 3) :
    griessProd (trialityABCBasis s (griessPairIndex i j hij))
      (trialityABCBasis t (griessPairIndex j k hjk)) =
      if s = t then (2 : ℝ) • trialityABCBasis s (griessPairIndex i k hik) else 0 := by
  have hpq := griessPairIndex_triangle_ne i j k hij hjk hik
  have hinc := griessPairIncidence_triangle i j k hij hjk hik
  have h00 := griessProd_of_raw_smul _ _ _ 2
    (conwayRawProduct_ABC_zero_triangle i j k hij hjk hik)
  have h11 := griessProd_of_raw_smul _ _ _ 2
    (conwayRawProduct_ABC_one_of_incidence _ _ _ hpq hinc)
  have h22 := griessProd_of_raw_smul _ _ _ 2
    (conwayRawProduct_ABC_two_of_incidence _ _ _ hpq hinc)
  have h01 := griessProd_of_raw_zero _ _
    (conwayRawProduct_ABC_zero_one_triangle i j k hij hjk hik)
  have h02 := griessProd_of_raw_zero _ _
    (conwayRawProduct_ABC_zero_two_triangle i j k hij hjk hik)
  have h12 := griessProd_of_raw_zero _ _
    (conwayRawProduct_ABC_one_two_of_incidence _ _ _ hpq hinc)
  have h10 := griessProd_of_raw_zero _ _
    (conwayRawProduct_ABC_zero_one_triangle k j i hjk.symm hij.symm hik.symm)
  have h20 := griessProd_of_raw_zero _ _
    (conwayRawProduct_ABC_zero_two_triangle k j i hjk.symm hij.symm hik.symm)
  rw [griessPairIndex_swap k j hjk.symm, griessPairIndex_swap j i hij.symm,
    griessProd_comm] at h10 h20
  have h21 := griessProd_of_raw_zero _ _
    (conwayRawProduct_ABC_one_two_of_incidence _ _ _ hpq.symm
      (by rw [add_comm]; exact hinc))
  rw [griessProd_comm] at h21
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
  all_goals norm_num [h00, h11, h22, h01, h02, h12, h10, h20, h21]

theorem sExtra_preserves_ABC_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t : Fin 3) :
    sExtra (griessProd (trialityABCBasis s (griessPairIndex i j hij))
      (trialityABCBasis t (griessPairIndex j k hjk))) =
      griessProd (sExtra (trialityABCBasis s (griessPairIndex i j hij)))
        (sExtra (trialityABCBasis t (griessPairIndex j k hjk))) := by
  rw [sExtra_ABC_basis, sExtra_ABC_basis,
    griessProd_ABC_triangle i j k hij hjk hik s t,
    griessProd_ABC_triangle i j k hij hjk hik (trialityCycle s) (trialityCycle t)]
  by_cases h : s = t
  · subst t
    simp only [ite_true, map_smul, sExtra_ABC_basis]
  · have hc : trialityCycle s ≠ trialityCycle t := fun he => h (trialityCycle.injective he)
    simp only [h, hc, ite_false, map_zero]


theorem conwayRawProduct_pair_short_disjoint (s : Fin 2) (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2) :
    conwayRawProduct (trialityPairMatrix p, (0, 0))
      (conwayShortBasis (Sum.inl (s, q))) = 0 := by
  have hv : griessShortVector (Sum.inl (s, q)) (griessCoordinatePair p).1 = 0 := by
    rw [griessShortVector, griessPairIntegral_off_support s q _ h11 h12]
    simp
  rw [trialityPairMatrix_raw_shortBasis, trialityPairMatrix_short_pairing, hv,
    mul_zero, zero_mul, zero_smul]

theorem conwayRawProduct_ABC_disjoint (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2) (s t : Fin 3) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis s p))
      (griessConwayEncode (trialityABCBasis t q)) = 0 := by
  have h00 := conwayRawProduct_ABC_zero_disjoint p q h11 h12 h21 h22
  have hp (s t : Fin 2) := conwayRawProduct_pairBasis_disjoint s t p q h11 h12 h21 h22
  have ha (s : Fin 2) := conwayRawProduct_pair_short_disjoint s p q h11 h12
  have hb (s : Fin 2) := conwayRawProduct_pair_short_disjoint s q p h11.symm h21.symm
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
  · exact h00
  · rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_one_short,
      conwayRawProduct_sub_right, ha, ha, sub_self]
  · rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_two_short,
      conwayRawProduct_add_right, ha, ha, add_zero]
  · rw [conwayRawProduct_comm, griessConwayEncode_ABC_zero_sparse,
      griessConwayEncode_ABC_one_short, conwayRawProduct_sub_right, hb, hb, sub_self]
  · rw [griessConwayEncode_ABC_one_short, griessConwayEncode_ABC_one_short,
      conwayRawProduct_sub_left, conwayRawProduct_sub_right,
      conwayRawProduct_sub_right, hp, hp, hp, hp, sub_self]
  · rw [griessConwayEncode_ABC_one_short, griessConwayEncode_ABC_two_short,
      conwayRawProduct_sub_left, conwayRawProduct_add_right,
      conwayRawProduct_add_right, hp, hp, hp, hp, add_zero, sub_self]
  · rw [conwayRawProduct_comm, griessConwayEncode_ABC_zero_sparse,
      griessConwayEncode_ABC_two_short, conwayRawProduct_add_right, hb, hb, add_zero]
  · rw [griessConwayEncode_ABC_two_short, griessConwayEncode_ABC_one_short,
      conwayRawProduct_add_left, conwayRawProduct_sub_right,
      conwayRawProduct_sub_right, hp, hp, hp, hp, sub_self, add_zero]
  · rw [griessConwayEncode_ABC_two_short, griessConwayEncode_ABC_two_short,
      conwayRawProduct_add_left, conwayRawProduct_add_right,
      conwayRawProduct_add_right, hp, hp, hp, hp, add_zero, add_zero]

theorem griessProd_ABC_disjoint (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2) (s t : Fin 3) :
    griessProd (trialityABCBasis s p) (trialityABCBasis t q) = 0 :=
  griessProd_of_raw_zero _ _ (conwayRawProduct_ABC_disjoint p q h11 h12 h21 h22 s t)

theorem sExtra_preserves_ABC_disjoint (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2) (s t : Fin 3) :
    sExtra (griessProd (trialityABCBasis s p) (trialityABCBasis t q)) =
      griessProd (sExtra (trialityABCBasis s p)) (sExtra (trialityABCBasis t q)) := by
  rw [sExtra_ABC_basis, sExtra_ABC_basis,
    griessProd_ABC_disjoint p q h11 h12 h21 h22 s t,
    griessProd_ABC_disjoint p q h11 h12 h21 h22 (trialityCycle s) (trialityCycle t), map_zero]


/-- Triality preserves the full 828-dimensional pair block product. The proof separates
coincident edges, edges sharing a vertex, and disjoint edges. -/
theorem sExtra_preserves_ABC_product (p q : Fin 276) (s t : Fin 3) :
    sExtra (griessProd (trialityABCBasis s p) (trialityABCBasis t q)) =
      griessProd (sExtra (trialityABCBasis s p)) (sExtra (trialityABCBasis t q)) := by
  by_cases hpq : p = q
  · subst q
    exact sExtra_preserves_ABC_same_pair p s t
  · have hindices : griessPairIndex (griessCoordinatePair p).1 (griessCoordinatePair p).2
        (griessCoordinatePair_ne p) ≠
        griessPairIndex (griessCoordinatePair q).1 (griessCoordinatePair q).2
          (griessCoordinatePair_ne q) := by
      simpa only [griessPairIndex_pair] using hpq
    rcases pairIndex_edges_cases _ _ _ _ (griessCoordinatePair_ne p)
        (griessCoordinatePair_ne q) hindices with htriangle | hdisjoint
    · rcases htriangle with ⟨i, j, k, hij, hjk, hik, hp, hq⟩
      simp only [griessPairIndex_pair] at hp hq
      rw [hp, hq]
      exact sExtra_preserves_ABC_triangle i j k hij hjk hik s t
    · exact sExtra_preserves_ABC_disjoint p q hdisjoint.1 hdisjoint.2.1
        hdisjoint.2.2.1 hdisjoint.2.2.2 s t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
