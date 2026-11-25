/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MatrixDiscrepancy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Kunisky's lower bound for the Komlós constant

We prove that the Komlós constant is at least `1 + Real.sqrt 2` using the recursive
Haar matrices in Kunisky's proof of Theorem 1.1.
-/

open scoped BigOperators ENNReal Topology
open Filter MatrixDiscrepancy

namespace KomlosDiscrepancyWanted

/-- **Kunisky's lower bound for the Komlós constant (statement).** The statement that the Komlós
constant is at least $1 + \sqrt{2}$.

The bound concerns the supremum over all dimensions; it does not assert that any single
dimension attains $1 + \sqrt{2}$.

Source: optimization catalogue C24a, line 45, and retained Kunisky
arXiv2111.02974v1, Theorem 1.1. -/
@[expose] public def kunisky2023LowerBound : Prop :=
  ENNReal.ofReal (1 + Real.sqrt 2) ≤ komlosConstant

private noncomputable def haarScale : ℝ := Real.sqrt 2 / 2

private theorem haarScale_nonneg : 0 ≤ haarScale := by
  unfold haarScale
  positivity

private theorem haarScale_sq : haarScale ^ 2 = 1 / 2 := by
  unfold haarScale
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Haar recursion doubles the dimension by adjoining an identity and a negative identity. -/
private noncomputable def haarStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  haarScale • Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 1 A (-1))

private theorem haarStep_admissible {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ColumnAdmissible A) : ColumnAdmissible (haarStep A) := by
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.sum_univ_add, haarStep, Matrix.smul_apply, smul_eq_mul,
      Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
      mul_pow, haarScale_sq, ← Finset.mul_sum]
    linarith [hA j]
  · norm_num [Fin.sum_univ_add, haarStep, -Fin.natAdd_eq_addNat, Matrix.one_apply, mul_pow,
      haarScale_sq, ← Finset.mul_sum, ite_pow]

private theorem abs_add_or_sub (a b : ℝ) :
    |a + b| = |a| + |b| ∨ |a - b| = |a| + |b| := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · left
    rw [abs_of_nonneg (add_nonneg ha hb), abs_of_nonneg ha, abs_of_nonneg hb]
  · right
    rw [abs_of_nonneg (by linarith : 0 ≤ a - b), abs_of_nonneg ha, abs_of_nonpos (le_of_not_ge hb)]
    ring
  · right
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), abs_of_nonpos (le_of_not_ge ha), abs_of_nonneg hb]
    ring
  · left
    rw [abs_of_nonpos (by linarith : a + b ≤ 0), abs_of_nonpos (le_of_not_ge ha),
      abs_of_nonpos (le_of_not_ge hb)]
    ring

private theorem haarStep_signing {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {d : ℝ}
    (hA : ∀ x : Fin n → Fin 2, ∃ i, |A.mulVec (fun j => signValue (x j)) i| = d)
    (x : Fin (n + n) → Fin 2) :
    ∃ i, |(haarStep A).mulVec (fun j => signValue (x j)) i| = haarScale * (d + 1) := by
  let left : Fin n → Fin 2 := fun j => x (Fin.castAdd n j)
  obtain ⟨i, hi⟩ := hA left
  let a := A.mulVec (fun j => signValue (left j)) i
  let b := signValue (x (Fin.natAdd n i))
  have hleft : (haarStep A).mulVec (fun j => signValue (x j)) (Fin.castAdd n i) =
      haarScale * (a + b) := by
    simp [haarStep, Matrix.smul_mulVec, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec,
      a, b, left, Function.comp_def]
  have hright : (haarStep A).mulVec (fun j => signValue (x j)) (Fin.natAdd n i) =
      haarScale * (a - b) := by
    simp [haarStep, Matrix.smul_mulVec, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec,
      Matrix.neg_mulVec, -Fin.natAdd_eq_addNat, a, b, left, sub_eq_add_neg, Function.comp_def]
  have ha : |a| = d := hi
  have hb : |b| = 1 := abs_signValue _
  rcases abs_add_or_sub a b with h | h
  · exact ⟨Fin.castAdd n i, by rw [hleft, abs_mul, abs_of_nonneg haarScale_nonneg, h, ha, hb]⟩
  · exact ⟨Fin.natAdd n i, by rw [hright, abs_mul, abs_of_nonneg haarScale_nonneg, h, ha, hb]⟩

/-- The closed form for the discrepancy lower bound after `k` doublings. -/
private noncomputable def haarBound (k : ℕ) : ℝ :=
  1 + Real.sqrt 2 - Real.sqrt 2 * haarScale ^ k

private theorem haarBound_succ (k : ℕ) : haarBound (k + 1) = haarScale * (haarBound k + 1) := by
  have hfixed : haarScale * (1 + Real.sqrt 2 + 1) = 1 + Real.sqrt 2 := by
    unfold haarScale
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [haarBound, pow_succ]
  linear_combination -hfixed

private theorem exists_haar_matrix (k : ℕ) :
    ∃ A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ, ColumnAdmissible A ∧
      ∀ x : Fin (2 ^ k) → Fin 2, ∃ i, |A.mulVec (fun j => signValue (x j)) i| = haarBound k := by
  induction k with
  | zero =>
    refine ⟨fun _ _ => 1, columnAdmissible_unit, fun x => ⟨0, ?_⟩⟩
    simp [Matrix.mulVec, dotProduct, haarBound]
  | succ k ih =>
    obtain ⟨A, hA, hx⟩ := ih
    rw [pow_succ, Nat.mul_two, haarBound_succ]
    exact ⟨haarStep A, haarStep_admissible hA, haarStep_signing hx⟩

private theorem ofReal_haarBound_le (k : ℕ) :
    ENNReal.ofReal (haarBound k) ≤ komlosConstant := by
  obtain ⟨A, hA, hx⟩ := exists_haar_matrix k
  have hk : 1 ≤ (2 : ℕ) ^ k := Nat.succ_le_of_lt (pow_pos (by decide) _)
  refine le_trans ?_ (le_iSup _ (⟨2 ^ k, hk⟩ : {n : ℕ // 1 ≤ n}))
  refine le_trans ?_ (le_iSup _ ⟨A, hA⟩)
  obtain ⟨x, heq⟩ := discrepancy_attained A
  obtain ⟨i, hi⟩ := hx x
  rw [heq, ← hi]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (A.mulVec (fun j => signValue (x j))) i

private theorem tendsto_haarBound :
    Tendsto haarBound atTop (𝓝 (1 + Real.sqrt 2)) := by
  have hlt : haarScale < 1 := by
    nlinarith [haarScale_sq, sq_nonneg (haarScale - 1)]
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one haarScale_nonneg hlt
  change Tendsto (fun k => 1 + Real.sqrt 2 - Real.sqrt 2 * haarScale ^ k) atTop _
  simpa only [mul_zero, sub_zero] using
    (tendsto_const_nhds (x := 1 + Real.sqrt 2)).sub (hpow.const_mul (Real.sqrt 2))

/-- **Kunisky's lower bound for the Komlós constant.** The Komlós constant (the supremum over all
$n \ge 1$ of the discrepancy of real $n \times n$ matrices whose columns all have Euclidean norm
at most $1$, taken in $[0, \infty]$) is at least $1 + \sqrt{2}$.

Source: Kunisky, arXiv2111.02974v1, Theorem 1.1; catalogue C24a, line 45. -/
public theorem kunisky2023LowerBound_holds : kunisky2023LowerBound := by
  exact le_of_tendsto' (ENNReal.continuous_ofReal.continuousAt.tendsto.comp tendsto_haarBound)
    ofReal_haarBound_le

end KomlosDiscrepancyWanted
