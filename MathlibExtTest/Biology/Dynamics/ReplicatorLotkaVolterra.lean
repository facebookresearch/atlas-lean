/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ReplicatorLotkaVolterra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tests for the orbital equivalence of replicator and Lotka–Volterra dynamics.

**Replicator to Lotka–Volterra.** Two strategies (`Option Unit`; `none` is the reference
strategy) with payoff matrix `A = lvGame 1 1`, i.e. rows `(1, 1)` for `some ()` and `(0, 0)` for
`none`. The replicator solution is the logistic curve `x(t) = (eᵗ, 1) / (1 + eᵗ)`, and the
corresponding Lotka–Volterra equation is `y' = y (1 + y)`. The explicit time change is
`τ(t) = ∫₀ᵗ 1 / (1 + eˢ) ds = log 2 + t - log (1 + eᵗ)`, the Lotka–Volterra trajectory is
`y(u) = eᵘ / (2 - eᵘ)`, and `y(τ(t)) = eᵗ = x_some(t) / x_none(t)`. Time is not preserved:
`τ(t) < log 2` for all `t ≥ 0` (the Lotka–Volterra solution blows up at `u = log 2` while the
replicator solution exists for all time), and `τ(t) < t` for `t > 0`.

**Lotka–Volterra to replicator.** The one-species equation `y' = -y` (game `lvGame (-1) 0`) with
`y(τ) = e^{-τ}`: the time change is `t(τ) = τ + 1 - e^{-τ}`, and the replicator trajectory at
time `t(τ)` is `(e^{-τ}, 1) / (1 + e^{-τ})`. -/

open Real Set Matrix

namespace MathlibExtTest.Biology.Dynamics.ReplicatorLotkaVolterra

open MathlibExt.Biology.Dynamics.Replicator MathlibExt.Biology.Dynamics.ReplicatorLotkaVolterra

/-! ### Smoke tests for the coordinate changes -/

example (α β γ δ x y : ℝ) :
    lvField ![α, -γ] !![0, -β; δ, 0] ![x, y] 0 = α * x - β * x * y := by
  rw [lvField_predatorPrey]
  rfl

example : toLV (ofLV (fun _ : Unit => (3 : ℝ))) () = 3 := by
  rw [toLV_ofLV (by norm_num)]

example : ∑ k, ofLV (fun _ : Unit => (3 : ℝ)) k = 1 := sum_ofLV (by norm_num)

example : lvGrowth (lvGame (fun _ : Unit => (5 : ℝ)) (Matrix.of fun _ _ => 7)) () = 5 := by simp

/-! ### Replicator to Lotka–Volterra: the logistic game -/

/-- The two-strategy game `lvGame 1 1`: payoff rows `(1, 1)` and `(0, 0)`. -/
def game : Matrix (Option Unit) (Option Unit) ℝ := lvGame (fun _ => 1) (Matrix.of fun _ _ => 1)

/-- The logistic replicator solution `x(t) = (eᵗ, 1) / (1 + eᵗ)`. -/
noncomputable def logistic (t : ℝ) : Option Unit → ℝ := ofLV fun _ => exp t

@[simp] theorem logistic_none (t : ℝ) : logistic t none = 1 / (1 + exp t) := by
  simp [logistic]

@[simp] theorem logistic_some (t : ℝ) (u : Unit) :
    logistic t (some u) = exp t / (1 + exp t) := by
  simp [logistic]

theorem game_mulVec (z : Option Unit → ℝ) :
    (game *ᵥ z) none = 0 ∧ (game *ᵥ z) (some ()) = z none + z (some ()) := by
  simp [game, lvGame, mulVec, dotProduct, Fintype.sum_option]

/-- **Non-vacuity witness.** The logistic curve solves the replicator equation of `game`. -/
theorem isSolution_logistic : IsSolution (fun z => game *ᵥ z) logistic where
  hasDerivAt k t _ := by
    have hpos : (1 + exp t) ≠ 0 := by positivity
    have hd : HasDerivAt (fun s => 1 + exp s) (exp t) t := (hasDerivAt_exp t).const_add 1
    have hmean : meanFitness (fun z => game *ᵥ z) (logistic t) = exp t / (1 + exp t) := by
      simp only [meanFitness, Fintype.sum_option, Fintype.sum_unique, (game_mulVec _).1,
        (game_mulVec _).2, logistic_none, logistic_some]
      field_simp
      ring
    cases k with
    | none =>
      have h := (hasDerivAt_const t (1 : ℝ)).fun_div hd hpos
      simp only [logistic_none, hmean, (game_mulVec _).1]
      convert h using 1
      field_simp
    | some u =>
      have h := (hasDerivAt_exp t).fun_div hd hpos
      cases u
      simp only [logistic_some, logistic_none, hmean, (game_mulVec _).2]
      convert h using 1
      field_simp

theorem logistic_pos (k : Option Unit) : 0 < logistic 0 k :=
  ofLV_pos (fun _ => exp_pos 0) k

theorem logistic_sum : ∑ k, logistic 0 k = 1 := sum_ofLV (by positivity)

/-- **The time change, explicitly.** `τ(t) = log 2 + t - log (1 + eᵗ)` for `t ≥ 0`. -/
theorem timeChange_logistic {t : ℝ} (ht : 0 ≤ t) :
    timeChange logistic t = log 2 + t - log (1 + exp t) := by
  have hF : ∀ s, HasDerivAt (fun s => s - log (1 + exp s)) (1 / (1 + exp s)) s := by
    intro s
    have h1 : (1 + exp s) ≠ 0 := by positivity
    have := (hasDerivAt_id' s).fun_sub (((hasDerivAt_exp s).const_add 1).log h1)
    convert this using 1
    field_simp
    ring_nf
  have hcont : Continuous fun s => logistic (max s 0) none := by
    simp only [logistic_none]
    exact continuous_const.div (continuous_const.add
      (continuous_exp.comp (continuous_id.max continuous_const))) fun s => by positivity
  rw [timeChange, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => s - log (1 + exp s))
    (fun s hs => ?_) (hcont.intervalIntegrable _ _)]
  · simp only [exp_zero, zero_sub]
    norm_num
    ring
  · rw [uIcc_of_le ht] at hs
    simpa [max_eq_left hs.1] using hF s

/-- The explicit Lotka–Volterra solution `y(u) = eᵘ / (2 - eᵘ)` of `y' = y (1 + y)`, which
blows up at `u = log 2`. -/
noncomputable def yLV (u : ℝ) : Unit → ℝ := fun _ => exp u / (2 - exp u)

/-- `yLV` solves the Lotka–Volterra equation of `game` before its blow-up time. -/
theorem hasDerivAt_yLV {u : ℝ} (hu : exp u ≠ 2) :
    HasDerivAt (fun v => yLV v ()) (lvField (lvGrowth game) (lvInteraction game) (yLV u) ()) u := by
  have h2 : (2 - exp u) ≠ 0 := sub_ne_zero.2 hu.symm
  have h := (hasDerivAt_exp u).fun_div ((hasDerivAt_exp u).const_sub 2) h2
  simp only [yLV, lvField, game, lvGrowth_lvGame, lvInteraction_lvGame, Fintype.sum_unique,
    Matrix.of_apply]
  convert h using 1
  field_simp
  ring

/-- **Orbit correspondence with the explicit time change.** The Lotka–Volterra trajectory
built from the logistic replicator solution is `yLV`, run at the time `τ(t)`:
`lvTrajectory logistic (τ t) = yLV (τ t) = eᵗ`. -/
theorem lvTrajectory_logistic {t : ℝ} (ht : 0 ≤ t) :
    lvTrajectory logistic (timeChange logistic t) () = exp t ∧
      yLV (timeChange logistic t) () = exp t := by
  obtain ⟨-, -, -, h, -⟩ := replicator_orbitEquiv_lotkaVolterra isSolution_logistic logistic_pos
    logistic_sum
  refine ⟨?_, ?_⟩
  · rw [(h t ht ()).1, logistic_some, logistic_none]
    field_simp
  · have h1 : (1 + exp t) ≠ 0 := by positivity
    rw [timeChange_logistic ht, yLV, exp_sub, exp_add, exp_log (by norm_num),
      exp_log (by positivity)]
    field_simp
    ring

/-- The Lotka–Volterra trajectory solves `y' = y (1 + y)` at each time `τ(t)`. -/
example {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => lvTrajectory logistic u ())
      (lvTrajectory logistic (timeChange logistic t) () *
        (1 + lvTrajectory logistic (timeChange logistic t) ())) (timeChange logistic t) := by
  obtain ⟨-, -, -, h, -⟩ := replicator_orbitEquiv_lotkaVolterra isSolution_logistic logistic_pos
    logistic_sum
  simpa [lvField, game, Matrix.of_apply] using (h t ht ()).2.2

/-- **Time is not preserved**: the Lotka–Volterra time never reaches `log 2`, although the
replicator solution exists for all `t ≥ 0`. -/
theorem timeChange_logistic_lt_log_two {t : ℝ} (ht : 0 ≤ t) : timeChange logistic t < log 2 := by
  rw [timeChange_logistic ht]
  have : t < log (1 + exp t) := by
    have h := log_lt_log (exp_pos t) (show exp t < 1 + exp t by linarith)
    rwa [log_exp] at h
  linarith

/-- **Time is not preserved**: `τ(1) ≠ 1`, from the general bound `τ(t) < t`. -/
example : timeChange logistic 1 ≠ 1 :=
  (timeChange_lt_self isSolution_logistic (continuous_const.matrix_mulVec continuous_id)
    logistic_pos logistic_sum one_pos).ne

/-! ### Lotka–Volterra to replicator: exponential decay -/

/-- The one-species game `lvGame (-1) 0`, whose Lotka–Volterra equation is `y' = -y`. -/
def decayGame : Matrix (Option Unit) (Option Unit) ℝ := lvGame (fun _ => -1) 0

/-- The positive Lotka–Volterra solution `y(τ) = e^{-τ}`. -/
noncomputable def decay (τ : ℝ) : Unit → ℝ := fun _ => exp (-τ)

theorem hasDerivAt_decay (i : Unit) (τ : ℝ) (_ : 0 ≤ τ) :
    HasDerivAt (fun σ => decay σ i)
      (lvField (lvGrowth decayGame) (lvInteraction decayGame) (decay τ) i) τ := by
  simp only [decay, lvField, decayGame, lvGrowth_lvGame, lvInteraction_lvGame,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  convert (hasDerivAt_neg τ).exp using 1

theorem decay_pos (τ : ℝ) (_ : 0 ≤ τ) (i : Unit) : 0 < decay τ i := exp_pos _

/-- **The time change, explicitly.** `t(τ) = τ + 1 - e^{-τ}` for `τ ≥ 0`. -/
theorem repTimeChange_decay {τ : ℝ} (hτ : 0 ≤ τ) : repTimeChange decay τ = τ + 1 - exp (-τ) := by
  have hcont : Continuous fun σ => 1 + ∑ j, decay (max σ 0) j := by
    simp only [decay, Fintype.sum_unique]
    exact continuous_const.add (continuous_exp.comp (continuous_id.max continuous_const).neg)
  rw [repTimeChange, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun σ => σ - exp (-σ)) (fun σ hσ => ?_) (hcont.intervalIntegrable _ _)]
  · simp only [neg_zero, exp_zero]
    ring
  · rw [uIcc_of_le hτ] at hσ
    simp only [decay, Fintype.sum_unique, max_eq_left hσ.1]
    convert (hasDerivAt_id' σ).fun_sub (hasDerivAt_neg σ).exp using 1
    ring

/-- **Orbit correspondence with the explicit time change.** `repTrajectory decay` solves the
replicator equation of `decayGame`, and at time `t(τ) = τ + 1 - e^{-τ}` it is
`(e^{-τ}, 1) / (1 + e^{-τ})`. -/
theorem repTrajectory_decay {τ : ℝ} (hτ : 0 ≤ τ) :
    IsSolution (fun z => decayGame *ᵥ z) (repTrajectory decay) ∧
      repTrajectory decay (τ + 1 - exp (-τ)) none = 1 / (1 + exp (-τ)) ∧
      repTrajectory decay (τ + 1 - exp (-τ)) (some ()) = exp (-τ) / (1 + exp (-τ)) := by
  obtain ⟨-, -, -, hsol, htraj, -, -⟩ :=
    lotkaVolterra_orbitEquiv_replicator hasDerivAt_decay decay_pos
  rw [← repTimeChange_decay hτ, htraj τ hτ]
  simp [decay, hsol]

/-- **Time is not preserved**: `t(1) = 2 - e^{-1} ≠ 1`. -/
example : repTimeChange decay 1 ≠ 1 := by
  rw [repTimeChange_decay zero_le_one]
  have : exp (-1) < 1 := by simp
  intro h
  linarith

#print axioms replicator_orbitEquiv_lotkaVolterra
#print axioms lotkaVolterra_orbitEquiv_replicator
#print axioms hasDerivAt_comp_invFun
#print axioms lvTrajectory_logistic
#print axioms timeChange_logistic_lt_log_two
#print axioms repTrajectory_decay

end MathlibExtTest.Biology.Dynamics.ReplicatorLotkaVolterra
