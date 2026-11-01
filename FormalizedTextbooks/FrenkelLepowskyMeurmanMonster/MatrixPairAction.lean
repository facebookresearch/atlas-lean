/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact sparse off-diagonal symmetric matrices in Conway's dictionary,
and their actions on the short and tensor coordinate blocks.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityBasisVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The symmetric elementary matrix E_ab+E_ba for the actual dictionary pair p=(a,b). -/
noncomputable def trialityPairMatrix (p : Fin 276) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.vecMulVec (Pi.single (griessCoordinatePair p).1 1)
    (Pi.single (griessCoordinatePair p).2 1) +
  Matrix.vecMulVec (Pi.single (griessCoordinatePair p).2 1)
    (Pi.single (griessCoordinatePair p).1 1)

/-- The two exact nonzero entries of the elementary symmetric matrix. -/
theorem trialityPairMatrix_apply (p : Fin 276) (i j : Fin 24) :
    trialityPairMatrix p i j =
      (if i = (griessCoordinatePair p).1 ∧ j = (griessCoordinatePair p).2 then 1 else 0) +
      (if i = (griessCoordinatePair p).2 ∧ j = (griessCoordinatePair p).1 then 1 else 0) := by
  classical
  simp only [trialityPairMatrix, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- Every diagonal entry of the off-diagonal dictionary matrix is zero. -/
theorem trialityPairMatrix_diagonal (p : Fin 276) (i : Fin 24) : trialityPairMatrix p i i = 0 := by
  rw [trialityPairMatrix_apply]
  have hn := griessCoordinatePair_ne p
  have h1 : ¬(i = (griessCoordinatePair p).1 ∧ i = (griessCoordinatePair p).2) := by
    rintro ⟨hi, hj⟩
    exact hn (hi.symm.trans hj)
  have h2 : ¬(i = (griessCoordinatePair p).2 ∧ i = (griessCoordinatePair p).1) := by
    rintro ⟨hi, hj⟩
    exact hn (hj.symm.trans hi)
  simp only [ite_eq_right h1, ite_eq_right h2, add_zero]

/-- The off-diagonal dictionary matrix has trace zero. -/
theorem trialityPairMatrix_trace (p : Fin 276) : Matrix.trace (trialityPairMatrix p) = 0 := by
  change (∑ i, trialityPairMatrix p i i) = 0
  simp only [trialityPairMatrix_diagonal, Finset.sum_const_zero]

private theorem pair_index_eq_iff (p : Fin 276) (i j : Fin 24) (h : i ≠ j) :
    griessPairIndex i j h = p ↔
      (i = (griessCoordinatePair p).1 ∧ j = (griessCoordinatePair p).2) ∨
      (i = (griessCoordinatePair p).2 ∧ j = (griessCoordinatePair p).1) := by
  constructor
  · intro hp
    have hc := congrArg griessCoordinatePair hp
    rw [griessPairIndex_coordinates] at hc
    split_ifs at hc with hij
    · exact Or.inl ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩
    · exact Or.inr ⟨congrArg Prod.snd hc, congrArg Prod.fst hc⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact griessPairIndex_pair p
    · rw [griessPairIndex_swap]
      exact griessPairIndex_pair p

/-- The A dictionary basis vector encodes as its elementary symmetric matrix alone. -/
theorem griessConwayEncode_ABC_zero_sparse (p : Fin 276) :
    griessConwayEncode (trialityABCBasis 0 p) = (trialityPairMatrix p, (0, 0)) := by
  rw [griessConwayEncode_ABC_basis]
  apply Prod.ext
  · dsimp only
    funext i j
    by_cases hij : i = j
    · subst j
      simp only [dite_true, trialityPairMatrix_diagonal]
    · rw [dite_eq_right hij, trialityPairMatrix_apply]
      simp only [Pi.single_eq_same, Pi.single_apply, pair_index_eq_iff]
      have hn := griessCoordinatePair_ne p
      by_cases hi1 : i = (griessCoordinatePair p).1 <;>
        by_cases hi2 : i = (griessCoordinatePair p).2 <;>
        by_cases hj1 : j = (griessCoordinatePair p).1 <;>
        by_cases hj2 : j = (griessCoordinatePair p).2 <;>
        simp_all
  · apply Prod.ext
    · funext r
      rcases r with ⟨u, q⟩ | (r | r) <;> simp
    · rfl

private theorem pair_matrix_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (v : I → ℝ) :
    (∑ i, ∑ j,
      ((if i = a ∧ j = b then (1 : ℝ) else 0) +
        (if i = b ∧ j = a then 1 else 0)) * v i * v j) = 2 * v a * v b := by
  simp only [ite_and, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The short pairing with E_ab+E_ba is exactly twice the product of those short coordinates. -/
theorem trialityPairMatrix_short_pairing (p : Fin 276) (r : GriessShortIndex) :
    conwayShortPairing (trialityPairMatrix p) r =
      2 * griessShortVector r (griessCoordinatePair p).1 *
        griessShortVector r (griessCoordinatePair p).2 := by
  unfold conwayShortPairing
  simp only [trialityPairMatrix_apply]
  exact pair_matrix_pairing _ _ _

private theorem pair_matrix_row {I : Type*} [Fintype I] [DecidableEq I]
    (a b i : I) (v : I → ℝ) :
    (∑ j, ((if j = a ∧ i = b then (1 : ℝ) else 0) +
        (if j = b ∧ i = a then 1 else 0)) * v j) =
      (if i = b then v a else 0) + (if i = a then v b else 0) := by
  simp only [ite_and, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The tensor action of the elementary symmetric matrix swaps its two indicated spatial rows. -/
theorem trialityPairMatrix_tensor_apply (p : Fin 276) (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    (∑ j, trialityPairMatrix p j i * T t j) =
      (if i = (griessCoordinatePair p).1 then T t (griessCoordinatePair p).2 else 0) +
      (if i = (griessCoordinatePair p).2 then T t (griessCoordinatePair p).1 else 0) := by
  simp only [trialityPairMatrix_apply]
  rw [pair_matrix_row]
  exact add_comm _ _

/-- The elementary dictionary matrix is symmetric. -/
theorem trialityPairMatrix_symmetric (p : Fin 276) (i j : Fin 24) :
    trialityPairMatrix p i j = trialityPairMatrix p j i := by
  simp only [trialityPairMatrix, Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

/-- Left multiplication by the elementary matrix exchanges its two spatial rows. -/
theorem trialityPairMatrix_mul_apply (p : Fin 276) (M : Matrix (Fin 24) (Fin 24) ℝ)
    (i j : Fin 24) :
    (trialityPairMatrix p * M) i j =
      (if i = (griessCoordinatePair p).1 then M (griessCoordinatePair p).2 j else 0) +
      (if i = (griessCoordinatePair p).2 then M (griessCoordinatePair p).1 j else 0) := by
  rw [Matrix.mul_apply]
  simp_rw [trialityPairMatrix_symmetric p i, trialityPairMatrix_apply]
  rw [pair_matrix_row]
  exact add_comm _ _

/-- Squaring E_ab+E_ba gives E_aa+E_bb, with the actual distinct dictionary coordinates. -/
theorem trialityPairMatrix_square (p : Fin 276) :
    trialityPairMatrix p * trialityPairMatrix p =
      Matrix.vecMulVec (Pi.single (griessCoordinatePair p).1 1)
        (Pi.single (griessCoordinatePair p).1 1) +
      Matrix.vecMulVec (Pi.single (griessCoordinatePair p).2 1)
        (Pi.single (griessCoordinatePair p).2 1) := by
  ext i j
  rw [trialityPairMatrix_mul_apply]
  simp only [trialityPairMatrix_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  have hn := griessCoordinatePair_ne p
  by_cases hi1 : i = (griessCoordinatePair p).1 <;>
    by_cases hi2 : i = (griessCoordinatePair p).2 <;>
    by_cases hj1 : j = (griessCoordinatePair p).1 <;>
    by_cases hj2 : j = (griessCoordinatePair p).2 <;>
    simp_all

/-- A pure elementary matrix multiplies each short coordinate by its exact coordinate pairing. -/
theorem trialityPairMatrix_raw_short (p : Fin 276) (M : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ) (r : GriessShortIndex) :
    (conwayRawProduct (trialityPairMatrix p, (0, 0)) (M, (X, T))).2.1 r =
      (2 * griessShortVector r (griessCoordinatePair p).1 *
        griessShortVector r (griessCoordinatePair p).2) * X r := by
  dsimp only [conwayRawProduct]
  simp only [Pi.zero_apply, zero_mul, mul_zero, add_zero, Finset.sum_const_zero,
    zero_div, spinOperator, LinearMap.coe_mk, AddHom.coe_mk, ite_self]
  rw [trialityPairMatrix_short_pairing]

/-- A pure elementary matrix acts on the tensor block by the exact spatial row swap. -/
theorem trialityPairMatrix_raw_tensor (p : Fin 276) (M : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (trialityPairMatrix p, (0, 0)) (M, (X, T))).2.2 t i =
      (if i = (griessCoordinatePair p).1 then T t (griessCoordinatePair p).2 else 0) +
      (if i = (griessCoordinatePair p).2 then T t (griessCoordinatePair p).1 else 0) := by
  dsimp only [conwayRawProduct]
  have hzero (q : Q) : spinOperator q (fun _ : SpinIndex => (0 : ℝ)) t = 0 :=
    congrFun ((spinOperator q).map_zero) t
  simp only [Pi.zero_apply, hzero, trialityPairMatrix_trace, zero_div,
    zero_mul, mul_zero, add_zero, Finset.sum_const_zero]
  exact trialityPairMatrix_tensor_apply p T t i

/-- Multiplying an elementary matrix with matrix-free coordinates produces no matrix component. -/
theorem trialityPairMatrix_raw_matrix_zero (p : Fin 276)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ) :
    (conwayRawProduct (trialityPairMatrix p, (0, 0)) (0, (X, T))).1 = 0 := by
  funext i j
  simp only [conwayRawProduct, Pi.zero_apply, Matrix.zero_apply,
    zero_mul, mul_zero, add_zero, Finset.sum_const_zero, zero_div, ite_self, zero_add]

/-- The full elementary-matrix action on the matrix-free short/tensor coordinates. -/
theorem trialityPairMatrix_raw_restriction (p : Fin 276)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ) :
    conwayRawProduct (trialityPairMatrix p, (0, 0)) (0, (X, T)) =
      (0, ((fun r => (2 * griessShortVector r (griessCoordinatePair p).1 *
        griessShortVector r (griessCoordinatePair p).2) * X r),
      (fun t i =>
        (if i = (griessCoordinatePair p).1 then T t (griessCoordinatePair p).2 else 0) +
        (if i = (griessCoordinatePair p).2 then T t (griessCoordinatePair p).1 else 0)))) := by
  apply Prod.ext
  · exact trialityPairMatrix_raw_matrix_zero p X T
  · apply Prod.ext
    · funext r
      exact trialityPairMatrix_raw_short p 0 X T r
    · funext t i
      exact trialityPairMatrix_raw_tensor p 0 X T t i

/-- The raw product gives four times the ordinary elementary matrix square. -/
theorem trialityPairMatrix_raw_square (p : Fin 276) :
    conwayRawProduct (trialityPairMatrix p, (0, 0)) (trialityPairMatrix p, (0, 0)) =
      ((4 : ℝ) • (trialityPairMatrix p * trialityPairMatrix p), (0, 0)) := by
  apply Prod.ext
  · funext i j
    simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
      ite_self, Finset.sum_const_zero, zero_div, Matrix.smul_apply,
      Matrix.mul_apply, smul_eq_mul, Finset.sum_add_distrib]
    ring
  · apply Prod.ext
    · funext r
      simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
        ite_self, Finset.sum_const_zero, zero_div]
    · funext t i
      simp only [conwayRawProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero,
        Finset.sum_const_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
