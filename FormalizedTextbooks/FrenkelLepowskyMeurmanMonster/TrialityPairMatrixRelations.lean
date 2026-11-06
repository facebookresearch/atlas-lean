/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MatrixPairAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary
/-! Exact pair-short coefficient matrices in Conway's tensor product.

For the physical minus and plus pair vectors, their coefficient matrices
sum to twice the identity minus eight times the projection onto the two
coordinate positions. Their difference is eight times the elementary
symmetric pair matrix. The character also stays fixed under all-one code
translation. Source: Seysen, arXiv:2002.10921v3, Table 5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
-- The coefficient matrices are presented through the matrix abbreviation.
set_option backward.isDefEq.respectTransparency false

noncomputable def trialityPairProjection (p : Fin 276) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.diagonal (fun i => (if i = (griessCoordinatePair p).1 then 1 else 0) +
    (if i = (griessCoordinatePair p).2 then 1 else 0))

noncomputable def trialityPairTensorMatrix (s : Fin 2) (p : Fin 276) :
    Matrix (Fin 24) (Fin 24) ℝ := fun i j => conwayTensorCoefficient (Sum.inl (s,p)) i j

lemma griessPair_outer_coordinate_sum (p : Fin 276) (i j : Fin 24) :
    griessShortVector (Sum.inl (0,p)) i * griessShortVector (Sum.inl (0,p)) j +
      griessShortVector (Sum.inl (1,p)) i * griessShortVector (Sum.inl (1,p)) j =
      4 * trialityPairProjection p i j := by
  have hn := griessCoordinatePair_ne p
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  simp only [griessShortVector, griessShortIntegral, trialityPairProjection,
    Matrix.diagonal_apply]
  push_cast
  rw [div_mul_div_comm, div_mul_div_comm, hs]
  by_cases hia : i = (griessCoordinatePair p).1 <;>
    by_cases hib : i = (griessCoordinatePair p).2 <;>
    by_cases hja : j = (griessCoordinatePair p).1 <;>
    by_cases hjb : j = (griessCoordinatePair p).2 <;>
    by_cases hij : i = j <;> simp_all <;> norm_num

lemma griessPair_outer_coordinate_difference (p : Fin 276) (i j : Fin 24) :
    griessShortVector (Sum.inl (1,p)) i * griessShortVector (Sum.inl (1,p)) j -
      griessShortVector (Sum.inl (0,p)) i * griessShortVector (Sum.inl (0,p)) j =
      4 * trialityPairMatrix p i j := by
  have hn := griessCoordinatePair_ne p
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  simp only [griessShortVector, griessShortIntegral, trialityPairMatrix_apply]
  push_cast
  rw [div_mul_div_comm, div_mul_div_comm, hs]
  by_cases hia : i = (griessCoordinatePair p).1 <;>
    by_cases hib : i = (griessCoordinatePair p).2 <;>
    by_cases hja : j = (griessCoordinatePair p).1 <;>
    by_cases hjb : j = (griessCoordinatePair p).2 <;> simp_all <;> norm_num

theorem trialityPairTensorMatrix_sum (p : Fin 276) :
    trialityPairTensorMatrix 0 p + trialityPairTensorMatrix 1 p =
      (2 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) - (8 : ℝ) • trialityPairProjection p := by
  ext i j
  simp only [trialityPairTensorMatrix, conwayTensorCoefficient, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h := griessPair_outer_coordinate_sum p i j
  linear_combination -2 * h

theorem trialityPairTensorMatrix_difference (p : Fin 276) :
    trialityPairTensorMatrix 0 p - trialityPairTensorMatrix 1 p =
      (8 : ℝ) • trialityPairMatrix p := by
  ext i j
  simp only [trialityPairTensorMatrix, conwayTensorCoefficient, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  have h := griessPair_outer_coordinate_difference p i j
  linear_combination 2 * h

lemma conwayTensorCoefficient_pair_sum (p : Fin 276) (i j : Fin 24) :
    conwayTensorCoefficient (Sum.inl (0,p)) i j +
      conwayTensorCoefficient (Sum.inl (1,p)) i j =
      2 * (if i = j then 1 else 0) - 8 * trialityPairProjection p i j := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i j)
    (trialityPairTensorMatrix_sum p)
  simpa only [trialityPairTensorMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using h

lemma conwayTensorCoefficient_pair_difference (p : Fin 276) (i j : Fin 24) :
    conwayTensorCoefficient (Sum.inl (0,p)) i j -
      conwayTensorCoefficient (Sum.inl (1,p)) i j = 8 * trialityPairMatrix p i j := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i j)
    (trialityPairTensorMatrix_difference p)
  simpa only [trialityPairTensorMatrix, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul] using h

lemma trialityPairProjection_tensor_apply (p : Fin 276) (v : Fin 24 → ℝ) (i : Fin 24) :
    (∑ j, trialityPairProjection p j i * v j) =
      ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0)) * v i := by
  simp only [trialityPairProjection, Matrix.diagonal_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

lemma griessPairSyndrome_dot_add_omega (p : Fin 276) (t : SpinIndex) :
    spinDot (griessPairSyndrome p) (t + Pi.single 11 1) =
      spinDot (griessPairSyndrome p) t := by
  rw [griessPairSyndrome_dot, griessPairSyndrome_dot, map_add, golay_all_one]
  simp only [Pi.add_apply]
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  calc
    _ = golayEncoder t (griessCoordinatePair p).1 +
      golayEncoder t (griessCoordinatePair p).2 + (1 + 1) := by ring
    _ = _ := by rw [htwo, add_zero]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
