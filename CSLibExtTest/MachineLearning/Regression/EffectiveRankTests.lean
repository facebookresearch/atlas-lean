/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.EffectiveRank
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NormNum

/-!
# Effective rank tests

For the identity covariance in dimension `p` (eigenvalues `1` repeated `p` times, then `0`),
both effective ranks at `k = 0` equal `p` (Bartlett, Long, Lugosi and Tsigler, the remark after
Lemma 5). Closed checks instantiate the chain `r_k(Σ²) ≤ r_k(Σ) ≤ R_k(Σ) ≤ r_k(Σ)²` for the
geometric spectrum `λ_{j+1} = 2^{-j}`.
-/

namespace Cslib.MachineLearning.EffectiveRank

private noncomputable def idSpec (p : ℕ) : ℕ → ℝ := fun j => if j < p then 1 else 0

private lemma tsum_idSpec (p : ℕ) : ∑' j, idSpec p (j + 0) = p := by
  rw [tsum_eq_sum (s := Finset.range p) (fun j hj => by
    simp [idSpec, Finset.mem_range.not.1 hj |> not_lt.1 |> not_lt.2])]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) fun j hj => by
    simp only [add_zero, idSpec, Finset.mem_range.1 hj, ↓reduceIte]]
  simp

private lemma tsum_idSpec_sq (p : ℕ) : ∑' j, idSpec p (j + 0) ^ 2 = p := by
  rw [tsum_eq_sum (s := Finset.range p) (fun j hj => by
    simp [idSpec, Finset.mem_range.not.1 hj |> not_lt.1 |> not_lt.2])]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) fun j hj => by
    simp only [add_zero, idSpec, Finset.mem_range.1 hj, ↓reduceIte, one_pow]]
  simp

example (p : ℕ) (hp : 0 < p) : effRank (idSpec p) 0 = p := by
  rw [effRank, tsum_idSpec]; simp [idSpec, hp]

example (p : ℕ) (hp : 0 < p) : effRankLarge (idSpec p) 0 = p := by
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [effRankLarge, tsum_idSpec, tsum_idSpec_sq]; field_simp

/-! Closed checks on the geometric spectrum. -/

private noncomputable def geom : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j

private lemma geom_nonneg (j : ℕ) : 0 ≤ geom j := by unfold geom; positivity
private lemma geom_anti : Antitone geom :=
  fun _ _ h => pow_le_pow_of_le_one (by norm_num) (by norm_num) h
private lemma geom_summable : Summable geom :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)
private lemma geom_pos (k : ℕ) : 0 < geom k := by unfold geom; positivity

example (k : ℕ) : 1 ≤ effRank geom k :=
  one_le_effRank geom_nonneg geom_summable (geom_pos k)

example (k : ℕ) : effRank (fun j => geom j ^ 2) k ≤ effRank geom k ∧
    effRank geom k ≤ effRankLarge geom k ∧ effRankLarge geom k ≤ effRank geom k ^ 2 :=
  ⟨effRank_sq_le_effRank geom_nonneg geom_anti geom_summable (geom_pos k),
    effRank_le_effRankLarge geom_nonneg geom_anti geom_summable (geom_pos k),
    effRankLarge_le_effRank_sq geom_nonneg geom_anti geom_summable (geom_pos k)⟩

end Cslib.MachineLearning.EffectiveRank
