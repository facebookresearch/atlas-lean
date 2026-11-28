/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.NeumannSeries

open scoped Topology ENNReal

@[expose] public section
namespace ContinuousLinearMap

/-- Two-state scene operator `T (x, y) = (x / 2, y / 3)`. -/
private noncomputable def sceneOp : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.prod ((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ)
    ((1 / 3 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Norm bound for the two-state scene operator. -/
private theorem sceneOp_norm : ‖sceneOp‖ ≤ 1 / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun p => ?_)
  have happ : sceneOp p = ((1 / 2 : ℝ) * p.1, (1 / 3 : ℝ) * p.2) := by
    simp [sceneOp]
  have h12 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]
    norm_num
  have h13 : ‖(1 / 3 : ℝ)‖ = 1 / 3 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [happ, Prod.norm_def, Prod.norm_def, norm_mul, norm_mul, h12, h13]
  refine max_le ?_ ?_
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  · calc (1 / 3 : ℝ) * ‖p.2‖ ≤ (1 / 3 : ℝ) * max ‖p.1‖ ‖p.2‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) * max ‖p.1‖ ‖p.2‖ :=
          mul_le_mul_of_nonneg_right (by norm_num)
            (le_trans (norm_nonneg _) (le_max_left _ _))

/-- Two-state exact scene: the fixed point `(2, 3 / 2)` for emission `(1, 1)`. -/
example : ((2 : ℝ), (3 / 2 : ℝ)) = neumannSeries sceneOp ((1 : ℝ), (1 : ℝ)) := by
  have hfix : ((2 : ℝ), (3 / 2 : ℝ))
      = ((1 : ℝ), (1 : ℝ)) + sceneOp ((2 : ℝ), (3 / 2 : ℝ)) := by
    have happ : sceneOp ((2 : ℝ), (3 / 2 : ℝ))
        = ((1 / 2 : ℝ) * 2, (1 / 3 : ℝ) * (3 / 2)) := by simp [sceneOp]
    rw [happ]
    norm_num [Prod.mk_add_mk, Prod.ext_iff]
  exact eq_neumannSeries_apply sceneOp (1 / 2) sceneOp_norm (by norm_num) hfix

/-- With `T = 0`, the Neumann series is the identity. -/
example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : E) : neumannSeries (0 : E →L[ℝ] E) x = x := by
  have h := neumannSeries_apply_eq_add (0 : E →L[ℝ] E) 0 (by simp) (by norm_num) x
  simpa using h

/-- Instance of the fixed-point equation at `x = 0`. -/
example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (c : ℝ) (hT : ‖T‖ ≤ c) (hc : c < 1) :
    neumannSeries T 0 = 0 + T (neumannSeries T 0) :=
  neumannSeries_apply_eq_add T c hT hc 0

/-- Zero emission gives zero response. -/
example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) : neumannSeries T 0 = 0 :=
  map_zero (neumannSeries T)

/-- Scaling operator `T x = x / 2` on `ℝ`. -/
private noncomputable def scaleOp : ℝ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- Norm bound for the scaling operator. -/
private theorem scaleOp_norm : ‖scaleOp‖ ≤ 1 / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => ?_)
  have happ : scaleOp x = (1 / 2 : ℝ) * x := by simp [scaleOp]
  have h12 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [happ, norm_mul, h12]

/-- Numeric instance of the truncation bound at `K = 0` on `ℝ`. -/
example : ‖neumannSeries scaleOp 1
    - ∑ k ∈ Finset.range (0 + 1), (scaleOp ^ k) 1‖
    ≤ (1 / 2 : ℝ) ^ (0 + 1) * ‖(1 : ℝ)‖ / (1 - 1 / 2) :=
  norm_neumannSeries_apply_sub_sum_le scaleOp (1 / 2) scaleOp_norm (by norm_num)
    (by norm_num) 1 0

/-- The left-hand side above evaluates to `1`. -/
example : ‖neumannSeries scaleOp 1
    - ∑ k ∈ Finset.range (0 + 1), (scaleOp ^ k) 1‖ = 1 := by
  show ‖neumannSeries scaleOp 1 - ∑ k ∈ Finset.range 1, (scaleOp ^ k) 1‖ = 1
  rw [Finset.sum_range_one, pow_zero, one_apply_eq_self]
  have h2 : (2 : ℝ) = 1 + scaleOp 2 := by
    have happ : scaleOp 2 = (1 / 2 : ℝ) * 2 := by simp [scaleOp]
    rw [happ]
    norm_num
  have hS1 : (2 : ℝ) = neumannSeries scaleOp 1 :=
    eq_neumannSeries_apply scaleOp (1 / 2) scaleOp_norm (by norm_num) h2
  rw [← hS1]
  norm_num [Real.norm_eq_abs]

/-- The right-hand side above evaluates to `1`. -/
example : (1 / 2 : ℝ) ^ (0 + 1) * ‖(1 : ℝ)‖ / (1 - 1 / 2) = 1 := by
  norm_num [Real.norm_eq_abs]

/-- The diagonal operator acts coordinatewise on arbitrary vectors, not just
singletons. -/
example (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) (n : ℕ) :
    (↑(lpDiag x) : (m : ℕ) → ℝ) n
      = (1 - 1 / (n + 1 : ℝ)) * (↑x : (m : ℕ) → ℝ) n :=
  lpDiag_apply_apply x n

/-- The strengthened existential acts coordinatewise on a non-singleton vector. -/
example (n : ℕ) :
    ∃ T : ↥(lp (fun _ : ℕ => ℝ) ⊤) →L[ℝ] ↥(lp (fun _ : ℕ => ℝ) ⊤),
      (↑(T (lp.single (E := fun _ : ℕ => ℝ) ⊤ 0 1
          + lp.single (E := fun _ : ℕ => ℝ) ⊤ 1 1)) : (m : ℕ) → ℝ) n
        = (1 - 1 / (n + 1 : ℝ))
          * (↑(lp.single (E := fun _ : ℕ => ℝ) ⊤ 0 1
            + lp.single (E := fun _ : ℕ => ℝ) ⊤ 1 1) : (m : ℕ) → ℝ) n
        ∧ ‖T‖ = 1 := by
  obtain ⟨T, hcoord, hnorm⟩ := exists_lp_diagonal_norm_eq_one
  exact ⟨T, hcoord _ n, hnorm⟩

end ContinuousLinearMap
