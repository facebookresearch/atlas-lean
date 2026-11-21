/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.PeriodicYeeError
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open MathlibExt.Analysis.Numerical
open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
open MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
open MathlibExt.Analysis.Numerical.PeriodicYeeResidual
open MathlibExt.Analysis.Numerical.PeriodicYeeError

namespace MathlibExtTest.Analysis.Numerical.PeriodicYeeError

/-! ### One cell, nonzero initial mismatch -/

/-- The zero pair is an admissible solution with zero derivative bounds. -/
private theorem zero_isSmoothPeriodicSolution (L c : ℝ) :
    isSmoothPeriodicSolution L c 0 0 (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> intros <;>
    simp [contDiff_const]

/-- On a one-cell grid both differences vanish, so the update is the identity. -/
private theorem leapfrogIterate_fin_one (h c dt : ℝ) (u0 v0 : Fin 1 → ℝ) (n : ℕ) :
    leapfrogIterate h c dt u0 v0 n = (u0, v0) := by
  have hs : ∀ j : Fin 1, periodicSucc j = j := fun _ => Subsingleton.elim _ _
  have hp : ∀ j : Fin 1, periodicPred j = j := fun _ => Subsingleton.elim _ _
  induction n with
  | zero => rfl
  | succ n ih =>
    change leapfrogStep h c dt (leapfrogIterate h c dt u0 v0 n).1
      (leapfrogIterate h c dt u0 v0 n).2 = (u0, v0)
    rw [ih]
    refine Prod.ext ?_ ?_ <;> funext j <;>
      simp [leapfrogStep, dPlusAdjoint_eq_neg_dMinus, dPlus, dMinus, hs, hp]

/-- Zero solution, initial data `u0 = 1`, `v0 = 0` on one cell with `h = 1`,
`dt = 1 / 2`: the initial mismatch is `1`. -/
private theorem oneCell_mismatch :
    initialPairMismatch (N := 1) (fun _ _ => 0) (fun _ _ => 0) 1 (1 / 2)
      (fun _ => 1) 0 = 1 := by
  simp [initialPairMismatch, pairNorm, pairNormSq, weightedNormSq,
    weightedInner, sampledU, sampledV]

/-- At the same data the pair error is `1` at every step: the mismatch never decays,
and the error at step `0` is the mismatch. -/
example (n : ℕ) :
    leapfrogPairError (N := 1) (fun _ _ => 0) (fun _ _ => 0) 1 1 (1 / 2)
        (fun _ => 1) 0 n = 1 ∧
      leapfrogPairError (N := 1) (fun _ _ => 0) (fun _ _ => 0) 1 1 (1 / 2)
        (fun _ => 1) 0 0 = 1 := by
  refine ⟨?_, (leapfrogPairError_zero _ _ _ _ _ _ _).trans oneCell_mismatch⟩
  simp [leapfrogPairError, leapfrogIterate_fin_one, pairNorm, pairNormSq,
    weightedNormSq, weightedInner, sampledU, sampledV]

/-- The global bound at the one-cell data with `c = 1`, `rho = 3 / 5`, `L = 1`,
`Mt = Mx = 0`: every step with `n * dt ≤ T` has pair error at most
`2 * (1 + 0) = 2`, and the bound is carried entirely by the mismatch. -/
example (n : ℕ) (T : ℝ) (hn : (n : ℝ) * (1 / 2) ≤ T) :
    leapfrogPairError (N := 1) (fun _ _ => 0) (fun _ _ => 0) 1 1 (1 / 2)
      (fun _ => 1) 0 n ≤ 2 := by
  have hb := leapfrogPairError_le (N := 1) one_pos 1 (1 / 2) 1 1 0 0 (3 / 5) T one_pos
    (by norm_num) one_pos (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
    (fun _ _ => 0) (fun _ _ => 0) (zero_isSmoothPeriodicSolution 1 1) (fun _ => 1) 0 n hn
  have hK : Real.sqrt ((1 + 3 / 5) / (1 - 3 / 5)) = 2 := by
    rw [show ((1 + 3 / 5) / (1 - 3 / 5) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [oneCell_mismatch, globalErrorBound, hK] at hb
  linarith

/-! ### Two cells, alternating mode -/

/-- The alternating mode `(1, -1)` on two cells attains the forward-difference
bound `2 / h`. -/
private theorem alternating_weightedNorm_dPlus (h : ℝ) (hh : 0 < h) :
    weightedNorm h (dPlus h (![1, -1] : Fin 2 → ℝ)) =
      (2 / h) * weightedNorm h (![1, -1] : Fin 2 → ℝ) := by
  have s0 : periodicSucc (0 : Fin 2) = 1 := rfl
  have s1 : periodicSucc (1 : Fin 2) = 0 := rfl
  have hsq : weightedNormSq h (dPlus h (![1, -1] : Fin 2 → ℝ)) =
      (2 / h) ^ 2 * weightedNormSq h (![1, -1] : Fin 2 → ℝ) := by
    have hne : h ≠ 0 := hh.ne'
    simp only [weightedNormSq, weightedInner, dPlus, Fin.sum_univ_two,
      s0, s1]
    simp
    field_simp
    ring
  rw [weightedNorm, weightedNorm, hsq, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity)]

/-- `weightedNorm_dPlus_le` holds with equality on the alternating mode. -/
example (h : ℝ) (hh : 0 < h) :
    weightedNorm h (dPlus h (![1, -1] : Fin 2 → ℝ)) ≤
      (2 / h) * weightedNorm h (![1, -1] : Fin 2 → ℝ) ∧
    (2 / h) * weightedNorm h (![1, -1] : Fin 2 → ℝ) ≤
      weightedNorm h (dPlus h (![1, -1] : Fin 2 → ℝ)) :=
  ⟨weightedNorm_dPlus_le h hh _, (alternating_weightedNorm_dPlus h hh).ge⟩

/-- No constant below `2 / h` bounds the forward difference on two cells, so the
operator bound `weightedNorm_dPlus_le` is sharp. This says nothing about
sharpness of the full forcing estimate or of the `1 / 6` constant. -/
example (h k : ℝ) (hh : 0 < h) (hk : k < 2 / h) :
    ¬ ∀ w : Fin 2 → ℝ, weightedNorm h (dPlus h w) ≤ k * weightedNorm h w := by
  intro hall
  have hpos : 0 < weightedNorm h (![1, -1] : Fin 2 → ℝ) := by
    unfold weightedNorm weightedNormSq weightedInner
    apply Real.sqrt_pos.mpr
    simp only [Fin.sum_univ_two]
    norm_num
    exact hh
  have h1 := hall ![1, -1]
  rw [alternating_weightedNorm_dPlus h hh] at h1
  have h2 := mul_lt_mul_of_pos_right hk hpos
  linarith

/-- Halving `dt` and `h` at `rho = 3 / 5`, `T = 1`, `L = 4`, `c = Mt = Mx = 1`,
`dt = 1 / 4`, `h = 1 / 2`, unit mismatch keeps the Courant number `1 / 2`
and divides the truncation term `5 / 48` by four. -/
example :
    (1 : ℝ) * (1 / 4 / 2) / (1 / 2 / 2) = 1 * (1 / 4) / (1 / 2) ∧
      globalErrorBound (3 / 5) 1 4 1 1 1 (1 / 4 / 2) (1 / 2 / 2) 1 =
        Real.sqrt ((1 + 3 / 5) / (1 - 3 / 5)) * (1 + (5 / 48) / 4) := by
  obtain ⟨hc, hb⟩ := globalErrorBound_refine_half (3 / 5) 1 4 1 1 1 (1 / 4) (1 / 2) 1
    (by norm_num)
  refine ⟨hc, hb.trans ?_⟩
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

end MathlibExtTest.Analysis.Numerical.PeriodicYeeError
