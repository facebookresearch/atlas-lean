/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.MirrorDescentEntropy

open Finset Real MathlibExt.Analysis.Convex.MirrorDescent

namespace MathlibExt.Analysis.Convex.MirrorDescentEntropy

-- The uniform point of `Δ₃` is in the relative interior.
example : uniform 3 ∈ posSimplex 3 := uniform_mem_posSimplex (by norm_num)

-- The entropy divergence from the uniform point of `Δ₃` to a vertex is at most `log 3`.
example : bregman entropy entropyDeriv (uniform 3) (WithLp.toLp 1 ![1, 0, 0]) ≤ log 3 := by
  refine bregman_entropy_uniform_le (by norm_num) ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp
  · simp [Fin.sum_univ_three]

-- ... and it equals `log 3` there: the bound is attained at the vertices.
example : bregman entropy entropyDeriv (uniform 3) (WithLp.toLp 1 ![1, 0, 0]) = log 3 := by
  rw [bregman_entropy_eq (uniform_mem_posSimplex (by norm_num)) (by simp [Fin.sum_univ_three])]
  simp [Fin.sum_univ_three, uniform_apply]

-- A linear form with coordinates in `[-2, 2]` has dual (`ℓ∞`) norm at most `2`.
example : ‖linearForm (n := 3) ![1, -2, 0]‖ ≤ 2 := by
  refine norm_le_of_abs_apply_single_le _ (by norm_num) fun i => ?_
  rw [linearForm_apply]
  fin_cases i <;> simp [PiLp.single_apply]

-- One Hedge step from the uniform point of `Δ₂` with losses `c = (0, 1)` and `γ = log 2`:
-- `x⁺ = (2/3, 1/3)`, and it satisfies the prox optimality condition with equality.
example (u : L1 2) (hu : ∑ i, u i = 1) :
    (log 2 • linearForm ![0, 1] - entropyDeriv (uniform 2) +
      entropyDeriv (WithLp.toLp 1 ![2 / 3, 1 / 3])) (u - WithLp.toLp 1 ![2 / 3, 1 / 3]) = 0 := by
  refine entropy_prox_multiplicative (uniform_mem_posSimplex (by norm_num))
    ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩
    (Z := 3 / 4) (by norm_num) (fun i => ?_) hu
  fin_cases i
  · simp [uniform_apply]; norm_num
  · simp [uniform_apply, exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

-- Strong convexity now reaches the vertices: from the uniform point of `Δ₃` to `e₁`.
example : 1 / 2 * ‖(WithLp.toLp 1 ![1, 0, 0] : L1 3) - uniform 3‖ ^ 2 ≤
    bregman entropy entropyDeriv (uniform 3) (WithLp.toLp 1 ![1, 0, 0]) := by
  refine bregman_entropy_ge (uniform_mem_posSimplex (by norm_num)) ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp
  · simp [Fin.sum_univ_three]

/-- One normalized multiplicative-weights (Hedge) step with losses `c` and rate `γ`. -/
noncomputable def hedgeStep {n : ℕ} (γ : ℝ) (c : Fin n → ℝ) (x : L1 n) : L1 n :=
  WithLp.toLp 1 fun i => x i * exp (-γ * c i) / ∑ j, x j * exp (-γ * c j)

theorem hedgeStep_mem {n : ℕ} (γ : ℝ) (c : Fin n → ℝ) {x : L1 n} (hx : x ∈ posSimplex n) :
    hedgeStep γ c x ∈ posSimplex n := by
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := by
    rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with h | h
    · have := hx.2; simp [h] at this
    · exact h
  have hZ : 0 < ∑ j, x j * exp (-γ * c j) :=
    Finset.sum_pos (fun j _ => mul_pos (hx.1 j) (exp_pos _)) hn
  refine ⟨fun i => div_pos (mul_pos (hx.1 i) (exp_pos _)) hZ, ?_⟩
  simp only [hedgeStep, PiLp.toLp_apply]
  rw [← Finset.sum_div, div_self hZ.ne']

/-- The Hedge trajectory from the uniform point with a fixed loss vector. -/
noncomputable def hedgeRun {n : ℕ} (γ : ℝ) (c : Fin n → ℝ) : ℕ → L1 n
  | 0 => uniform n
  | t + 1 => hedgeStep γ c (hedgeRun γ c t)

-- A multi-step Hedge run with losses `(0, 1)` on two experts: its regret against expert `0`
-- after `N` rounds is at most `log 2 / γ + γ N / 2`.
example (γ : ℝ) (hγ : 0 < γ) (N : ℕ) :
    ∑ t ∈ range N, (∑ j : Fin 2, (![0, 1] : Fin 2 → ℝ) j * hedgeRun γ ![0, 1] t j -
      (![0, 1] : Fin 2 → ℝ) 0) ≤ log 2 / γ + γ * N / 2 := by
  have hmem : ∀ t, hedgeRun γ ![0, 1] t ∈ posSimplex 2 := by
    intro t
    induction t with
    | zero => exact uniform_mem_posSimplex (by norm_num)
    | succ t ih => exact hedgeStep_mem _ _ ih
  have := multiplicative_weights_regret_le (n := 2) (by norm_num) hγ (c := fun _ => ![0, 1])
    (x := hedgeRun γ ![0, 1])
    (Z := fun t => ∑ j : Fin 2, hedgeRun γ ![0, 1] t j * exp (-γ * (![0, 1] : Fin 2 → ℝ) j))
    rfl hmem
    (fun t => by
      have h := hmem t
      exact Finset.sum_pos (fun j _ => mul_pos (h.1 j) (exp_pos _)) Finset.univ_nonempty)
    (fun t i => rfl) (fun t i => by fin_cases i <;> simp) 0 N
  simpa using this

end MathlibExt.Analysis.Convex.MirrorDescentEntropy
