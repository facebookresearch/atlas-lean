/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Product compatibility of the explicit dictionary triality.

This module proves the complete diagonal-factor case of Conway's AA, AX,
and AT multiplication rules. General non-diagonal and short/tensor cases
remain separate proof obligations for the milestone theorem.
Source: Conway, Invent. Math. 79 (1985), pp. 513–540, §12,
DOI: 10.1007/BF01388521; Seysen, arXiv:2002.10921v3, §8.1.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

noncomputable def trialityDiagonalVector (d : Fin 24 → ℝ) : GriessSpace :=
  trialityBlocksEquiv.symm (d, (0, (0, 0)))

theorem sExtra_diagonal (d : Fin 24 → ℝ) :
    sExtra (trialityDiagonalVector d) = trialityDiagonalVector d := by
  apply trialityBlocksEquiv.injective
  simp only [sExtra, griessTriality, trialityDiagonalVector, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, map_zero]

theorem griessConwayEncode_diagonal (d : Fin 24 → ℝ) :
    griessConwayEncode (trialityDiagonalVector d) =
      (Matrix.diagonal d, (0, 0)) := by
  simp only [griessConwayEncode, trialityDiagonalVector, LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  · funext r
    rcases r with ⟨s,p⟩ | (⟨o,e⟩ | ⟨a,i⟩) <;> simp
  · funext t i
    simp

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_diagonal (d : Fin 24 → ℝ) (x : ConwayRawSpace) :
    conwayRawProduct (Matrix.diagonal d, (0, 0)) x =
      ((fun i j => 2 * (d i + d j) * x.1 i j),
        ((fun r => conwayShortPairing (Matrix.diagonal d) r * x.2.1 r),
        (fun t i => (d i + (∑ j, d j) / 8) * x.2.2 t i))) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    simp [conwayRawProduct, Matrix.diagonal_apply, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq]
    ring
  · funext r
    simp [conwayRawProduct, conwayShortPairing, Matrix.diagonal_apply,
      Finset.sum_add_distrib, spinOperator]
  · funext t i
    simp [conwayRawProduct, Matrix.diagonal_apply, Matrix.trace,
      Finset.sum_add_distrib, spinOperator]
    ring

theorem griessShortVector_square (r : GriessShortIndex) (i : Fin 24) :
    griessShortVector r i ^ 2 = ((griessShortIntegral r i ^ 2 : ℤ) : ℝ) / 8 := by
  simp only [griessShortVector, div_pow, Int.cast_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

set_option backward.isDefEq.respectTransparency false in
theorem conwayShortPairing_diagonal (d : Fin 24 → ℝ) (r : GriessShortIndex) :
    conwayShortPairing (Matrix.diagonal d) r = ∑ i, d i * griessShortVector r i ^ 2 := by
  simp only [conwayShortPairing, Matrix.diagonal_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem griessPair_coordinate_square (s : Fin 2) (p : Fin 276) (i : Fin 24) :
    griessShortIntegral (Sum.inl (s,p)) i ^ 2 =
      (if i = (griessCoordinatePair p).1 then 16 else 0) +
      (if i = (griessCoordinatePair p).2 then 16 else 0) := by
  have hne := griessCoordinatePair_ne p
  by_cases hi : i = (griessCoordinatePair p).1
  · subst i
    simp only [griessShortIntegral, hne, ite_true, ite_false]
    split <;> norm_num
  · by_cases hj : i = (griessCoordinatePair p).2
    · subst i
      simp only [griessShortIntegral, hne.symm, ite_true, ite_false]
      split <;> norm_num
    · simp [griessShortIntegral, hi, hj]

theorem griessOctad_coordinate_square (o : Fin 759) (e : Fin 64) (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inl (o,e))) i ^ 2 =
      if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 4 else 0 := by
  simp only [griessShortIntegral]
  split_ifs <;> norm_num

set_option backward.isDefEq.respectTransparency false in
theorem conwayShortPairing_diagonal_pair (d : Fin 24 → ℝ) (s : Fin 2) (p : Fin 276) :
    conwayShortPairing (Matrix.diagonal d) (Sum.inl (s,p)) =
      2 * (d (griessCoordinatePair p).1 + d (griessCoordinatePair p).2) := by
  rw [conwayShortPairing_diagonal]
  simp_rw [griessShortVector_square, griessPair_coordinate_square]
  simp only [Int.cast_add, Int.cast_ite, Int.cast_ofNat, Int.cast_zero, add_div]
  simp only [ite_div, zero_div, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem conwayShortPairing_diagonal_octad (d : Fin 24 → ℝ) (o : Fin 759) (e : Fin 64) :
    conwayShortPairing (Matrix.diagonal d) (Sum.inr (Sum.inl (o,e))) =
      ∑ i, if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then d i / 2 else 0 := by
  rw [conwayShortPairing_diagonal]
  simp_rw [griessShortVector_square, griessOctad_coordinate_square]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num
  ring

set_option backward.isDefEq.respectTransparency false in
theorem conwayShortPairing_diagonal_odd (d : Fin 24 → ℝ) (a : Fin 2048) (j : Fin 24) :
    conwayShortPairing (Matrix.diagonal d) (Sum.inr (Sum.inr (a,j))) =
      d j + (∑ i, d i) / 8 := by
  rw [conwayShortPairing_diagonal]
  simp_rw [griessShortVector_square, griessOdd_coordinate_square]
  have hterm (i : Fin 24) : d i *
      ((↑(if i = j then (9 : ℤ) else 1) : ℝ) / 8) =
        d i / 8 + (if i = j then d i else 0) := by
    split_ifs <;> norm_num <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

noncomputable def trialityDiagonalOctadWeight (d : Fin 24 → ℝ) (o : Fin 759) : ℝ :=
  ∑ i, if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then d i / 2 else 0

noncomputable def trialityDiagonalBlocks (d : Fin 24 → ℝ) (b : TrialityBlocks) : TrialityBlocks :=
  ((fun i => 4 * d i * b.1 i),
    ((fun s p => 2 * (d (griessCoordinatePair p).1 + d (griessCoordinatePair p).2) * b.2.1 s p),
    ((fun o e => trialityDiagonalOctadWeight d o * b.2.2.1 o e),
    (fun s k => (d (finProdFinEquiv.symm k : Fin 2048 × Fin 24).2 +
      (∑ j, d j) / 8) * b.2.2.2 s k))))

theorem conwayDiagonalProduct_dictionary (d : Fin 24 → ℝ) (x : ConwayRawSpace) :
    trialityBlocksEquiv (griessConwayDecode
      (conwayRawProduct (Matrix.diagonal d, (0,0)) x)) =
    trialityDiagonalBlocks d (trialityBlocksEquiv (griessConwayDecode x)) := by
  rw [conwayRawProduct_diagonal]
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply, trialityDiagonalBlocks]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i
    dsimp only
    ring
  · funext s p
    dsimp only
    rw [conwayShortPairing_diagonal_pair, conwayShortPairing_diagonal_pair]
    rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl
    all_goals simp only [Fin.isValue, ite_true,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, ite_false]
    all_goals ring
  · funext o e
    dsimp only
    rw [conwayShortPairing_diagonal_octad]
    rfl
  · funext s k
    dsimp only
    rw [conwayShortPairing_diagonal_odd]
    rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl
    all_goals simp only [Fin.isValue, ite_true,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, ite_false]
    all_goals ring

theorem griessProd_diagonal_dictionary (d : Fin 24 → ℝ) (x : GriessSpace) :
    trialityBlocksEquiv (griessProd (trialityDiagonalVector d) x) =
      trialityDiagonalBlocks d (trialityBlocksEquiv x) := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_diagonal,
    conwayDiagonalProduct_dictionary, griessConwayDecode_encode]

/-- Diagonal multiplication commutes with all three parts of the actual triality. -/
theorem trialityDiagonalBlocks_triality (d : Fin 24 → ℝ) (b : TrialityBlocks) :
    trialityBlockAction (trialityDiagonalBlocks d b) =
      trialityDiagonalBlocks d (trialityBlockAction b) := by
  simp only [trialityBlockAction, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    trialityDiagonalBlocks]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext s p
    rfl
  · funext o
    simp only [LinearEquiv.piCongrRight_apply]
    exact (trialityOctadAction.map_smul (trialityDiagonalOctadWeight d o) (b.2.2.1 o))
  · funext s k
    rfl

/-- The extra symmetry preserves every product having a diagonal factor.
This covers the diagonal instances of Conway's AA, AX and AT rules. -/
theorem sExtra_preserves_diagonal_product (d : Fin 24 → ℝ) (x : GriessSpace) :
    sExtra (griessProd (trialityDiagonalVector d) x) =
      griessProd (sExtra (trialityDiagonalVector d)) (sExtra x) := by
  rw [sExtra_diagonal]
  apply trialityBlocksEquiv.injective
  have hcoord (v : GriessSpace) : trialityBlocksEquiv (sExtra v) =
      trialityBlockAction (trialityBlocksEquiv v) := by
    simp only [sExtra, griessTriality, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hcoord, griessProd_diagonal_dictionary, griessProd_diagonal_dictionary,
    hcoord, trialityDiagonalBlocks_triality]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
