/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Approximation.ApproximationGuarantee
import CSLibExt.Computability.Complexity.BoolClosure
import Mathlib.Tactic.NormNum

namespace CSLibExtTest.Algorithms.Lean.Approximation.ApproximationGuarantee

noncomputable section

open CSLibExt.Algorithms.Approximation
open Cslib.Complexity.Classes (OptProblem ApproxAt)
open MetaMathlibExt.ComplexityTheory

private def trial (lo hi : ℚ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (allowTrue : Bool := true) :
    OptProblem where
  feas _
    | [false] => true
    | [true] => allowTrue
    | _ => false
  val _
    | [false] => lo
    | [true] => if allowTrue then hi else 0
    | _ => 0
  bound := Polynomial.C 1
  feas_len x s hs := by
    cases s with
    | nil => simp at hs
    | cons b t =>
      cases t with
      | nil => simp
      | cons c t => cases b <;> simp at hs
  val_nonneg x s := by
    cases s with
    | nil => exact le_rfl
    | cons b t =>
      cases t with
      | nil => cases b <;> simp [hlo, hhi, apply_ite]
      | cons c t => cases b <;> exact le_rfl
  val_infeas x s hs := by
    cases s with
    | nil => rfl
    | cons b t =>
      cases t with
      | nil => cases b <;> simp_all
      | cons c t => cases b <;> rfl
  feas_nonempty _ := ⟨[false], rfl⟩

private def positiveTrial : OptProblem := trial 2 4 (by norm_num) (by norm_num)
private def zeroMinTrial : OptProblem := trial 0 4 le_rfl (by norm_num)
private def zeroMaxTrial : OptProblem := trial 0 0 le_rfl le_rfl
private def onlyFalse : OptProblem := trial 0 0 le_rfl le_rfl false

private theorem positiveTrial_cases {x s : List Bool} (hs : positiveTrial.feas x s = true) :
    s = [false] ∨ s = [true] := by
  cases s with
  | nil => simp [positiveTrial, trial] at hs
  | cons b t =>
    cases t with
    | nil => cases b <;> simp
    | cons c t => cases b <;> simp [positiveTrial, trial] at hs

private def fixed (b : Bool) : List Bool → List Bool := fun _ => [b]

private theorem fixed_polytime (b : Bool) : IsPolyTime (fixed b) :=
  (isPolyTime_dup.comp (isPolyTime_heads (fun _ _ => b))).comp isPolyTime_singleton

private def flip (q : List Bool × List Bool) : List Bool := [q.2.headD false]

private theorem flip_polytime : IsPolyTime flip :=
  (isPolyTime_heads (fun b _ => b)).comp isPolyTime_singleton

private theorem flip_feasible (x : List Bool) (r : List Bool) :
    positiveTrial.feas x (flip (x, r)) = true := by
  change positiveTrial.feas x [r.headD false] = true
  cases r.headD false <;> rfl

-- The deterministic solvers deliberately take the worse solution in each direction.
example : IsMinApproximation positiveTrial (fixed true) 2 := by
  refine ⟨fixed_polytime _, by norm_num, fun x => ⟨rfl, ?_⟩⟩
  intro s hs
  obtain rfl | rfl := positiveTrial_cases hs <;> norm_num [positiveTrial, trial, fixed]

private theorem deterministic_half : IsMaxApproximation positiveTrial (fixed false) (1 / 2) := by
  refine ⟨fixed_polytime _, by norm_num, by norm_num, fun x => ⟨rfl, ?_⟩⟩
  intro s hs
  obtain rfl | rfl := positiveTrial_cases hs <;> norm_num [positiveTrial, trial, fixed]

example (k : ℕ) : ApproxAt positiveTrial (fun q => fixed false q.1) k (1 / 2) := by
  apply (approxAt_iff_isMaxApproximation (fixed_polytime false) (by norm_num) (by norm_num)).2
  simpa using deterministic_half

-- Use the reciprocal convention at solver level, not just for an isolated score.
example (x : List Bool) :
    (positiveTrial.val x [true] : ℝ) / 2 ≤ (positiveTrial.val x (fixed false x) : ℝ) := by
  have h := (isMaxApproximation_iff_factor (by norm_num : (0 : ℝ) < 1 / 2)).mp
    deterministic_half
  simpa using (h.2.2 x).2 [true] rfl

private theorem flip_expected (lo hi : ℚ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (x : List Bool) :
    expectedValue (trial lo hi hlo hhi) flip x 1 = (lo + hi) / 2 := by
  unfold expectedValue
  rw [Fintype.expect_equiv (Equiv.funUnique (Fin 1) Bool) _ (fun b => if b then hi else lo)]
  · rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, Fintype.card_bool]
    simp [add_comm]
  · intro r
    rw [List.ofFn_succ, List.ofFn_zero]
    change (trial lo hi hlo hhi).val x [r 0] = if r 0 then hi else lo
    cases r 0 <;> rfl

-- One coin gives equal weight to outputs with values 2 and 4, so neither bound is pointwise.
private theorem positiveTrial_expected (x : List Bool) : expectedValue positiveTrial flip x 1 = 3 := by
  unfold positiveTrial
  rw [flip_expected]
  norm_num

example : IsRandomizedMinApproximation positiveTrial (Polynomial.C 1) flip (3 / 2) := by
  refine ⟨flip_polytime, by norm_num, fun x => ⟨fun r => flip_feasible x _, ?_⟩⟩
  intro s hs
  dsimp only
  rw [Polynomial.eval_C, positiveTrial_expected]
  obtain rfl | rfl := positiveTrial_cases hs <;> norm_num [positiveTrial, trial]

private theorem randomized_three_quarters :
    IsRandomizedMaxApproximation positiveTrial (Polynomial.C 1) flip (3 / 4) := by
  refine ⟨flip_polytime, by norm_num, by norm_num, fun x => ⟨fun r => flip_feasible x _, ?_⟩⟩
  intro s hs
  dsimp only
  rw [Polynomial.eval_C, positiveTrial_expected]
  obtain rfl | rfl := positiveTrial_cases hs <;> norm_num [positiveTrial, trial]

-- The expected value attains the multiplicative bound; the false tape does not.
example (x : List Bool) :
    (positiveTrial.val x [true] : ℝ) / (4 / 3) ≤ (expectedValue positiveTrial flip x 1 : ℝ) ∧
    (positiveTrial.val x (flip (x, [false])) : ℝ) < (3 / 4) * (positiveTrial.val x [true] : ℝ) := by
  constructor
  · have h := (isRandomizedMaxApproximation_iff_factor (by norm_num : (0 : ℝ) < 3 / 4)).mp
      randomized_three_quarters
    have hbound := (h.2.2 x).2 [true] rfl
    norm_num [Polynomial.eval_C] at hbound
    exact hbound
  · norm_num [positiveTrial, trial, flip]

-- Zero coins still produce one outcome.
example (x : List Bool) : expectedValue positiveTrial flip x 0 = 2 := by
  simp [expectedValue, List.ofFn_zero, flip, positiveTrial, trial]

-- The two feasible outputs cost 0 and 4. Only the zero-cost solver is exact.
example : IsApproximation zeroMinTrial .minimize (.deterministic (fixed false)) 1 := by
  refine ⟨fixed_polytime _, le_rfl, fun x => ⟨rfl, fun s _ => ?_⟩⟩
  simpa [zeroMinTrial, trial, fixed] using
    (show (0 : ℝ) ≤ (zeroMinTrial.val x s : ℝ) by exact_mod_cast zeroMinTrial.val_nonneg x s)

example (α : ℝ) : ¬ IsMinApproximation zeroMinTrial (fixed true) α := by
  intro h
  have hbad := (h.2.2 []).2 [false] rfl
  norm_num [zeroMinTrial, trial, fixed] at hbad

-- Both tapes are feasible but their mean cost is 2, so no finite ratio works.
example (α : ℝ) : ¬ IsRandomizedMinApproximation zeroMinTrial (Polynomial.C 1) flip α := by
  intro h
  have hmean : expectedValue zeroMinTrial flip [] 1 = 2 := by
    unfold zeroMinTrial
    rw [flip_expected]
    norm_num
  have hbad := (h.2.2 []).2 [false] rfl
  dsimp only at hbad
  rw [Polynomial.eval_C, hmean] at hbad
  norm_num [zeroMinTrial, trial] at hbad

-- A zero maximization optimum is also covered by the solver-level reciprocal bridge.
example : IsRandomizedMaxApproximation zeroMaxTrial (Polynomial.C 1) flip (1 / 2) := by
  apply (isRandomizedMaxApproximation_iff_factor (by norm_num : (0 : ℝ) < 1 / 2)).mpr
  have hzero (x s : List Bool) : zeroMaxTrial.val x s = 0 := by
    cases s with
    | nil => rfl
    | cons b t => cases t <;> cases b <;> rfl
  refine ⟨flip_polytime, by norm_num, fun x => ⟨?_, fun s _ => ?_⟩⟩
  · intro r
    change zeroMaxTrial.feas x [(List.ofFn r).headD false] = true
    cases (List.ofFn r).headD false <;> rfl
  · simp [expectedValue, hzero]

-- Neither a zero threshold nor an infeasible outcome can pass by giving everything value zero.
example : ¬ IsMaxApproximation zeroMaxTrial (fixed false) 0 := fun h => lt_irrefl 0 h.2.1

example : ¬ IsRandomizedMaxApproximation onlyFalse (Polynomial.C 1) flip 1 := by
  intro h
  have hbad := (h.2.2.2 []).1 (fun _ => true)
  have hcoin {n : ℕ} (hn : n = 1) : List.ofFn (fun _ : Fin n => true) = [true] := by
    subst n
    simp [List.ofFn_succ]
  rw [hcoin (Polynomial.eval_C (x := ([] : List Bool).length))] at hbad
  change false = true at hbad
  contradiction

end

end CSLibExtTest.Algorithms.Lean.Approximation.ApproximationGuarantee
