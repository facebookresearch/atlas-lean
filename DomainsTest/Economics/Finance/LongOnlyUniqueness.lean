/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.LongOnlyUniqueness
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

open MathlibExt.Probability.Finance.LongOnlyAttainment
open MathlibExt.Probability.Finance.LongOnlyUniqueness
open Matrix

namespace MathlibExt.Probability.Finance.LongOnlyUniqueness

/-- (a) Positive-definite 3-asset diagonal covariance, entries 1, 2, 3. -/
private def SigmaPD : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun (i j : Fin 3) => if i = j then ((i.val : ℝ) + 1) else 0

private theorem SigmaPD_mulVec (i : Fin 3) (d : Fin 3 → ℝ) :
    (SigmaPD *ᵥ d) i = ((i.val : ℝ) + 1) * d i := by
  simp only [Matrix.mulVec_apply_eq_sum, SigmaPD, Matrix.of_apply, ite_mul,
    zero_mul]
  rw [Finset.sum_ite_eq]
  simp

private theorem SigmaPD_quad (d : Fin 3 → ℝ) :
    d ⬝ᵥ (SigmaPD *ᵥ d) = ∑ i, (((i.val : ℝ) + 1) * (d i) ^ 2) := by
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [SigmaPD_mulVec]
  ring

private theorem SigmaPD_pos (d : Fin 3 → ℝ) (hd : d ≠ 0) :
    0 < d ⬝ᵥ (SigmaPD *ᵥ d) := by
  rw [SigmaPD_quad]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
  have hdi : d i ≠ 0 := by simpa using hi
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ i, mul_pos (by positivity) (sq_pos_of_ne_zero hdi)⟩

private theorem mem_pd :
    (![0, 1, 0] : Fin 3 → ℝ) ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · norm_num [dotProduct, Fin.sum_univ_three]

private theorem SigmaPD_eq_diagonal :
    SigmaPD = Matrix.diagonal (fun i : Fin 3 => ((i.val : ℝ) + 1)) := by
  ext i j
  simp only [SigmaPD, Matrix.of_apply, Matrix.diagonal_apply]

private theorem SigmaPD_isHermitian : SigmaPD.IsHermitian := by
  rw [SigmaPD_eq_diagonal]
  exact Matrix.isHermitian_diagonal _

private theorem SigmaPD_star_pos (d : Fin 3 → ℝ) (hd : d ≠ 0) :
    0 < star d ⬝ᵥ (SigmaPD *ᵥ d) := by
  have h := SigmaPD_pos d hd
  simpa using h

private theorem SigmaPD_posDef : SigmaPD.PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos SigmaPD_isHermitian
    (fun x hx => SigmaPD_star_pos x hx)

theorem pd_three_asset_existsUnique :
    ∃! w, w ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ) ∧
      IsMinOn (fun w => w ⬝ᵥ (SigmaPD *ᵥ w))
        (targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ)) w := by
  exact existsUnique_isMinOn_targetSlice_of_posDef SigmaPD _ _ ⟨_, mem_pd⟩ SigmaPD_posDef

/-- (b) Zero covariance: the objective vanishes identically. -/
private theorem psd_obj_zero (w : Fin 3 → ℝ) :
    (fun w => w ⬝ᵥ ((0 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w)) w = 0 := by
  simp only [Matrix.zero_mulVec, dotProduct_zero]

private theorem mem_psd_a :
    (![0, 1, 0] : Fin 3 → ℝ) ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · norm_num [dotProduct, Fin.sum_univ_three]

private theorem mem_psd_b :
    (![1 / 2, 0, 1 / 2] : Fin 3 → ℝ)
      ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · norm_num [dotProduct, Fin.sum_univ_three]

private theorem psd_min_a :
    IsMinOn (fun w : Fin 3 → ℝ => w ⬝ᵥ ((0 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w))
      (targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ)) ![0, 1, 0] := by
  rw [isMinOn_iff]
  intro x _
  simp only [psd_obj_zero]
  exact le_rfl

private theorem psd_min_b :
    IsMinOn (fun w : Fin 3 → ℝ => w ⬝ᵥ ((0 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w))
      (targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ)) ![1 / 2, 0, 1 / 2] := by
  rw [isMinOn_iff]
  intro x _
  simp only [psd_obj_zero]
  exact le_rfl

private theorem psd_ne :
    (![0, 1, 0] : Fin 3 → ℝ) ≠ ![1 / 2, 0, 1 / 2] := by
  intro h
  have h0 := congrFun h 0
  norm_num at h0

theorem psd_zero_not_unique :
    ¬ ∃! w, w ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ) ∧
      IsMinOn (fun w => w ⬝ᵥ ((0 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w))
        (targetSlice (![0, 1, 2] : Fin 3 → ℝ) (1 : ℝ)) w := by
  intro huniq
  obtain ⟨w₀, -, huniq'⟩ := huniq
  have e1 := huniq' _ ⟨mem_psd_a, psd_min_a⟩
  have e2 := huniq' _ ⟨mem_psd_b, psd_min_b⟩
  exact psd_ne (e1.trans e2.symm)

/-- (c) All-ones covariance: singular, boundary singleton slice. -/
private def SigmaOnes : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun (_ _ : Fin 3) => (1 : ℝ)

private theorem mem_single :
    (![1, 0, 0] : Fin 3 → ℝ) ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (0 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · norm_num [dotProduct, Fin.sum_univ_three]

private theorem single_of_mem :
    ∀ w ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (0 : ℝ), w = ![1, 0, 0] := by
  intro w hw
  obtain ⟨hwge, hws, hwd⟩ := hw
  have hdot : w 1 + 2 * w 2 = 0 := by
    have h : (![0, 1, 2] : Fin 3 → ℝ) ⬝ᵥ w = 0 * w 0 + 1 * w 1 + 2 * w 2 := by
      norm_num [dotProduct, Fin.sum_univ_three]
    rw [hwd] at h
    linarith
  have hw1 : w 1 = 0 := by linarith [hwge 1, hwge 2, hdot]
  have hw2 : w 2 = 0 := by linarith [hwge 1, hwge 2, hdot]
  have hw0 : w 0 = 1 := by
    have h : ∑ i, w i = w 0 + w 1 + w 2 := Fin.sum_univ_three _
    rw [hws] at h
    linarith
  funext i
  fin_cases i
  · simpa using hw0
  · simpa using hw1
  · simpa using hw2

theorem boundary_singleton_existsUnique :
    ∃! w, w ∈ targetSlice (![0, 1, 2] : Fin 3 → ℝ) (0 : ℝ) ∧
      IsMinOn (fun w => w ⬝ᵥ (SigmaOnes *ᵥ w))
        (targetSlice (![0, 1, 2] : Fin 3 → ℝ) (0 : ℝ)) w := by
  refine existsUnique_isMinOn_targetSlice_of_pair_pos SigmaOnes _ _ ⟨_, mem_single⟩ ?_
  intro w hw v hv hne'
  exfalso
  exact hne' ((single_of_mem w hw).trans (single_of_mem v hv).symm)

theorem allOnes_null_direction :
    (![1, -2, 1] : Fin 3 → ℝ) ⬝ᵥ (SigmaOnes *ᵥ ![1, -2, 1]) = 0 := by
  have hmv : ∀ i : Fin 3, (SigmaOnes *ᵥ ![1, -2, 1]) i = 0 := by
    intro i
    simp only [Matrix.mulVec_apply_eq_sum, SigmaOnes, Matrix.of_apply]
    norm_num [Fin.sum_univ_three]
  simp only [dotProduct, hmv, mul_zero, Finset.sum_const_zero]

end MathlibExt.Probability.Finance.LongOnlyUniqueness
