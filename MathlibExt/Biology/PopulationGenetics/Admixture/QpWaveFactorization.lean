/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Drift-model factorization of the qpWave f4 matrix

For a drift model, the qpWave matrix of `f4` statistics between left
populations `L` and right populations `R` factors through the lineage-weight
contrasts against the references `L 0` and `R 0`:
`F = W_L diag(len) W_Rᵀ`, where `W_L` and `W_R` are the contrast matrices of
weights. The rank of `F` is therefore bounded by the number of drift edges on
which both sides have a nonzero contrast, and by the ranks of the two
contrast matrices. In particular a right set whose contrasts all vanish gives
`F = 0` regardless of the left side.

## Main results

* `DriftModel.contrastMatrix`: lineage-weight contrasts against a reference.
* `DriftModel.f4Matrix_eq_contrast_mul_diagonal_mul_transpose`: the
  factorization `F = W_L diag(len) W_Rᵀ`.
* `DriftModel.rank_f4Matrix_le_support`: the support rank bound.
* `DriftModel.rank_f4Matrix_le_rank_contrast_right`,
  `DriftModel.rank_f4Matrix_le_rank_contrast_left`: contrast-rank bounds.
* `DriftModel.f4Matrix_eq_zero_of_weight_right_succ_eq`: an uninformative
  right set gives `F = 0`.

## References

* N. Patterson et al., "Ancient admixture in human history", *Genetics* 192
  (2012), 1065–1093 (the qpWave rank test).
* D. Reich et al., "Reconstructing Indian population history", *Nature* 461
  (2009), 489–494 (f4 statistics and matrix rank).
-/

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics
  MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

variable {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
  (M : DriftModel μ E P)

/-- Contrasts of the lineage weights of `L 1, …, L n` against `L 0`. -/
def contrastMatrix {n : ℕ} (L : Fin (n + 1) → P) : Matrix (Fin n) E ℝ :=
  Matrix.of fun i e => M.weight (L i.succ) e - M.weight (L 0) e

/-- Drift-model factorization: `F = (W_L - 1 w_L0^T) diag(len) (W_R - 1 w_R0^T)^T`. -/
theorem f4Matrix_eq_contrast_mul_diagonal_mul_transpose [DecidableEq E] {n r : ℕ}
    (L : Fin (n + 1) → P) (R : Fin (r + 1) → P) :
    ADMIXTOOLS.f4Matrix μ M.freq L R =
      M.contrastMatrix L * Matrix.diagonal M.len * (M.contrastMatrix R)ᵀ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [ADMIXTOOLS.f4Matrix, Matrix.of_apply, Matrix.mul_diagonal,
    Matrix.transpose_apply, contrastMatrix, M.f4_freq]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Support form of the bound: if outside a finset `S` of edges every left contrast or every right contrast vanishes, then `rank F ≤ S.card`. -/
theorem rank_f4Matrix_le_card_of_forall_not_mem {n r : ℕ} (L : Fin (n + 1) → P)
    (R : Fin (r + 1) → P) (S : Finset E)
    (hS : ∀ e ∉ S, (∀ i, M.contrastMatrix L i e = 0) ∨
      ∀ j, M.contrastMatrix R j e = 0) :
    (ADMIXTOOLS.f4Matrix μ M.freq L R).rank ≤ S.card := by
  classical
  let A : Matrix (Fin n) S ℝ :=
    Matrix.of fun i e => (M.weight (L i.succ) e.val - M.weight (L 0) e.val) * M.len e.val
  let B : Matrix S (Fin r) ℝ :=
    Matrix.of fun e j => M.weight (R j.succ) e.val - M.weight (R 0) e.val
  have hF : ADMIXTOOLS.f4Matrix μ M.freq L R = A * B := by
    ext i j
    set D : E → ℝ := fun e => (M.weight (L i.succ) e - M.weight (L 0) e) * M.len e *
      (M.weight (R j.succ) e - M.weight (R 0) e) with hD
    have hvanish : ∀ e ∉ S, D e = 0 := by
      intro e he
      rcases hS e he with hL | hR
      · have h0 := hL i
        simp only [contrastMatrix, Matrix.of_apply] at h0
        rw [hD]; simp only [h0]; ring
      · have h0 := hR j
        simp only [contrastMatrix, Matrix.of_apply] at h0
        rw [hD]; simp only [h0]; ring
    have hsum : (∑ e, D e) = ∑ e : S, D e.val := by
      rw [Finset.sum_coe_sort]
      exact (Finset.sum_subset (Finset.subset_univ S) (fun e _ he => hvanish e he)).symm
    calc ADMIXTOOLS.f4Matrix μ M.freq L R i j = ∑ e, D e := by
          simp only [ADMIXTOOLS.f4Matrix, Matrix.of_apply, M.f4_freq]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hD]; ring
      _ = ∑ e : S, D e.val := hsum
      _ = (A * B) i j := by
          simp [Matrix.mul_apply, A, B, hD]
  rw [hF]
  refine (Matrix.rank_mul_le_left A B).trans ?_
  exact (Matrix.rank_le_card_width A).trans_eq (Fintype.card_coe S)

/-- The rank of the qpWave f4 matrix is at most the number of edges on which both a left and a right contrast are nonzero. -/
theorem rank_f4Matrix_le_support {n r : ℕ} (L : Fin (n + 1) → P)
    (R : Fin (r + 1) → P) :
    (ADMIXTOOLS.f4Matrix μ M.freq L R).rank ≤
      Nat.card {e : E // (∃ i, M.contrastMatrix L i e ≠ 0) ∧
        ∃ j, M.contrastMatrix R j e ≠ 0} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply M.rank_f4Matrix_le_card_of_forall_not_mem L R
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_exists,
    ne_eq, Decidable.not_not] at he
  by_cases hL : ∀ i, M.contrastMatrix L i e = 0
  · exact Or.inl hL
  · refine Or.inr (he ?_)
    push Not at hL
    obtain ⟨i, hi⟩ := hL
    exact ⟨i, hi⟩

/-- `rank F` cannot exceed the rank of the right contrasts; rank lower bounds therefore need independent right contrasts. -/
theorem rank_f4Matrix_le_rank_contrast_right {n r : ℕ} (L : Fin (n + 1) → P)
    (R : Fin (r + 1) → P) :
    (ADMIXTOOLS.f4Matrix μ M.freq L R).rank ≤ (M.contrastMatrix R).rank := by
  classical
  rw [M.f4Matrix_eq_contrast_mul_diagonal_mul_transpose L R]
  refine (Matrix.rank_mul_le_right _ _).trans_eq ?_
  rw [Matrix.rank_transpose]

/-- `rank F` cannot exceed the rank of the left contrasts. -/
theorem rank_f4Matrix_le_rank_contrast_left {n r : ℕ} (L : Fin (n + 1) → P)
    (R : Fin (r + 1) → P) :
    (ADMIXTOOLS.f4Matrix μ M.freq L R).rank ≤ (M.contrastMatrix L).rank := by
  classical
  rw [M.f4Matrix_eq_contrast_mul_diagonal_mul_transpose L R]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)

/-- An uninformative right set: if every right population has the same lineage weights as the right reference, then `F = 0`. -/
theorem f4Matrix_eq_zero_of_weight_right_succ_eq {n r : ℕ} (L : Fin (n + 1) → P)
    (R : Fin (r + 1) → P) (hR : ∀ (j : Fin r) (e : E),
      M.weight (R j.succ) e = M.weight (R 0) e) :
    ADMIXTOOLS.f4Matrix μ M.freq L R = 0 := by
  classical
  rw [M.f4Matrix_eq_contrast_mul_diagonal_mul_transpose L R]
  have : M.contrastMatrix R = 0 := by
    ext j e
    simp [contrastMatrix, hR j e]
  rw [this]
  simp

end MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel
