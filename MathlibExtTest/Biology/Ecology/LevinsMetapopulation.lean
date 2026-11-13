/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Ecology.LevinsMetapopulation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for the Levins metapopulation model

Three concrete regimes, each with a trajectory written down and checked against the equation
from the definitions (derivative computed by hand, not through the theorems under test):

* `c = 2`, `e = 1` (persistence): `p* = 1/2`, and from `p(0) = 1/4` the solution
  `p(t) = 1 / (2 (1 + e^{-t}))` converges to `1/2`, with `|p(t) - 1/2| ≤ e^{-t} / 2`.
* `c = e = 1` (boundary): `p* = 0`, the linearization at `0` vanishes, and from `p(0) = 1` the
  solution `p(t) = 1 / (1 + t)` decays algebraically.
* `c = 1`, `e = 2` (extinction): from `p(0) = 1` the solution `p(t) = e^{-t} / (2 - e^{-t})`
  decays exponentially, `p(t) ≤ e^{-t}`.

A last example records the `c = 0` boundary: `persistenceEq 0 1 = 1` is not an equilibrium.
-/

open Real Filter Set
open scoped Topology

namespace MathlibExtTest.Biology.Ecology.LevinsMetapopulation

open MathlibExt.Biology.Ecology.LevinsMetapopulation

/-! ### The balance and the equilibria -/

example : balance 2 1 (1 / 4) = 1 / 8 := by norm_num [balance]

example : balance 2 1 (1 / 2) = 0 := by norm_num [balance]

example : balance 2 1 1 = -1 := by norm_num [balance]

/-! ### Persistence: `c = 2`, `e = 1` -/

/-- The persistence equilibrium, computed from the definition. -/
theorem persistenceEq_two_one : persistenceEq 2 1 = 1 / 2 := by norm_num [persistenceEq]

example : persistenceEq 2 1 ∈ Ioc (0 : ℝ) 1 :=
  (persistenceEq_mem_Ioc_iff (by norm_num) (by norm_num)).2 (by norm_num)

/-- Linearizations: `f'(0) = 1 > 0` (extinction unstable), `f'(1/2) = -1 < 0`. -/
example : HasDerivAt (balance 2 1) 1 0 := by
  have h := hasDerivAt_balance_zero (2 : ℝ) 1
  norm_num at h
  exact h

example : HasDerivAt (balance 2 1) (-1) (1 / 2) := by
  have h := hasDerivAt_balance_persistenceEq (c := 2) (e := 1) two_ne_zero
  rw [persistenceEq_two_one] at h
  norm_num at h
  exact h

/-- The explicit trajectory from `p(0) = 1/4`: `p(t) = 1 / (2 (1 + e^{-t}))`. -/
noncomputable def traj (t : ℝ) : ℝ := (2 * (1 + exp (-t)))⁻¹

theorem traj_zero : traj 0 = 1 / 4 := by norm_num [traj]

/-- `traj` solves `p' = 2 p (1 - p) - p` (derivative computed directly). -/
theorem isSolution_traj : IsSolution 2 1 traj := by
  refine ⟨fun t _ => ?_⟩
  have hu : HasDerivAt (fun s => exp (-s)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hden : 2 * (1 + exp (-t)) ≠ 0 := by positivity
  have h := ((hu.const_add 1).const_mul 2).inv hden
  refine h.congr_deriv ?_
  simp only [balance, traj]
  field_simp
  ring

/-- `traj → 1/2`, computed directly from `e^{-t} → 0`. -/
theorem tendsto_traj : Tendsto traj atTop (𝓝 (1 / 2)) := by
  have h := ((tendsto_exp_neg_atTop_nhds_zero.const_add 1).const_mul 2).inv₀
    (by norm_num : (2 : ℝ) * (1 + 0) ≠ 0)
  rw [show (1 / 2 : ℝ) = (2 * (1 + 0))⁻¹ by norm_num]
  exact h

/-- The direct limit is the persistence equilibrium. -/
example : Tendsto traj atTop (𝓝 (persistenceEq 2 1)) := by
  rw [persistenceEq_two_one]; exact tendsto_traj

/-- The global-stability theorem applies to `traj` and gives the same limit. -/
example : Tendsto traj atTop (𝓝 (persistenceEq 2 1)) :=
  (persistence_isGloballyStable (by norm_num) (by norm_num)).2 traj isSolution_traj
    (by rw [traj_zero]; norm_num)

/-- `traj` is the explicit solution `levins 2 1 (1/4)` on `[0, ∞)`. -/
example {t : ℝ} (ht : 0 ≤ t) : traj t = levins 2 1 (1 / 4) t := by
  rw [isSolution_traj.eq_levins (by norm_num) (by rw [traj_zero]; norm_num) ht, traj_zero]

/-- Exponential rate from `abs_levins_sub_le_exp`: `|p(t) - 1/2| ≤ e^{-t} / 2`. -/
example {t : ℝ} (ht : 0 ≤ t) : |levins 2 1 (1 / 4) t - 1 / 2| ≤ exp (-t) / 2 := by
  have h := abs_levins_sub_le_exp (c := 2) (e := 1) (by norm_num) (by norm_num)
    (p₀ := 1 / 4) (by norm_num) ht
  rw [persistenceEq_two_one] at h
  norm_num at h
  convert h using 1
  ring_nf

/-- The same bound, checked directly on `traj`: `1/2 - traj t = e^{-t} / (2 (1 + e^{-t}))`. -/
example (t : ℝ) : |traj t - 1 / 2| ≤ exp (-t) / 2 := by
  have hu := exp_pos (-t)
  have e1 : traj t - 1 / 2 = -(exp (-t) / (2 * (1 + exp (-t)))) := by
    simp only [traj]; field_simp; ring
  rw [e1, abs_neg, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) two_pos]
  nlinarith

/-- `traj` stays in `(0, 1/2)`. -/
example (t : ℝ) : traj t ∈ Ioo 0 (1 / 2) := by
  have hu := exp_pos (-t)
  refine ⟨by unfold traj; positivity, ?_⟩
  show (2 * (1 + exp (-t)))⁻¹ < 1 / 2
  rw [one_div]
  exact (inv_lt_inv₀ (by positivity) two_pos).2 (by linarith)

/-- Above the threshold, extinction is unstable. -/
example : ¬ IsLyapunovStable 2 1 0 (Icc 0 1) :=
  not_isLyapunovStable_zero (by norm_num) (by norm_num)

example : ¬ ∀ p : ℝ → ℝ, IsSolution 2 1 p → p 0 ∈ Icc 0 1 → Tendsto p atTop (𝓝 0) := by
  rw [tendsto_zero_iff_le (by norm_num) (by norm_num)]; norm_num

/-! ### Boundary: `c = e = 1` -/

example : persistenceEq 1 1 = 0 := by norm_num [persistenceEq]

/-- At `c = e` the persistence equilibrium is not an occupied state. -/
example : persistenceEq 1 1 ∉ Ioc (0 : ℝ) 1 := by
  rw [persistenceEq_mem_Ioc_iff one_pos zero_le_one]; norm_num

/-- The linearization at `0` vanishes: the boundary case is not decided by linear stability. -/
example : HasDerivAt (balance 1 1) 0 0 := by
  simpa using hasDerivAt_balance_zero (1 : ℝ) 1

/-- The boundary trajectory from `p(0) = 1`: `p(t) = 1 / (1 + t)`. -/
noncomputable def trajBdry (t : ℝ) : ℝ := (1 + t)⁻¹

/-- `trajBdry` solves `p' = p (1 - p) - p = -p²` on `[0, ∞)` (derivative computed directly). -/
theorem isSolution_trajBdry : IsSolution 1 1 trajBdry := by
  refine ⟨fun t ht => ?_⟩
  have hden : 1 + t ≠ 0 := by positivity
  have h := ((hasDerivAt_id t).const_add 1).inv hden
  refine h.congr_deriv ?_
  simp only [balance, trajBdry, id]
  field_simp
  ring

example : trajBdry 0 = 1 := by norm_num [trajBdry]

/-- Algebraic decay `1 / (1 + t) → 0`, computed directly. -/
theorem tendsto_trajBdry : Tendsto trajBdry atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)

/-- Global stability of extinction covers the boundary `c = e`. -/
example : Tendsto trajBdry atTop (𝓝 0) :=
  (extinction_isGloballyStable zero_le_one one_pos le_rfl).2 trajBdry isSolution_trajBdry
    (by norm_num [trajBdry])

example : ∀ p : ℝ → ℝ, IsSolution 1 1 p → p 0 ∈ Icc 0 1 → Tendsto p atTop (𝓝 0) :=
  (tendsto_zero_iff_le one_pos one_pos).2 le_rfl

/-! ### Extinction: `c = 1`, `e = 2` -/

/-- The extinction trajectory from `p(0) = 1`: `p(t) = e^{-t} / (2 - e^{-t})`. -/
noncomputable def trajExt (t : ℝ) : ℝ := exp (-t) / (2 - exp (-t))

example : trajExt 0 = 1 := by norm_num [trajExt]

/-- `e^{-t} ≤ 1` on `[0, ∞)`. -/
private theorem exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) : exp (-t) ≤ 1 :=
  exp_le_one_iff.2 (by linarith)

/-- `trajExt` solves `p' = p (1 - p) - 2 p` on `[0, ∞)` (derivative computed directly). -/
theorem isSolution_trajExt : IsSolution 1 2 trajExt := by
  refine ⟨fun t ht => ?_⟩
  have hu : HasDerivAt (fun s => exp (-s)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hden : 2 - exp (-t) ≠ 0 := by linarith [exp_neg_le_one ht]
  have hd : HasDerivAt (fun s => 2 - exp (-s)) (0 - -exp (-t)) t :=
    (hasDerivAt_const t (2 : ℝ)).sub hu
  have h := hu.div hd hden
  refine h.congr_deriv ?_
  simp only [balance, trajExt]
  field_simp
  ring

/-- **Explicit exponential decay**: `0 ≤ p(t) ≤ e^{-t}` on `[0, ∞)`. -/
theorem trajExt_le {t : ℝ} (ht : 0 ≤ t) : trajExt t ≤ exp (-t) := by
  have h1 := exp_neg_le_one ht
  exact div_le_self (exp_pos _).le (by linarith)

theorem trajExt_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ trajExt t :=
  div_nonneg (exp_pos _).le (by linarith [exp_neg_le_one ht])

/-- `trajExt → 0`, by squeezing between `0` and `e^{-t}`. -/
theorem tendsto_trajExt : Tendsto trajExt atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_exp_neg_atTop_nhds_zero
    (by filter_upwards [eventually_ge_atTop 0] with t ht using trajExt_nonneg ht)
    (by filter_upwards [eventually_ge_atTop 0] with t ht using trajExt_le ht)

/-- The extinction theorem agrees, and the trajectory never exceeds its initial value. -/
example : Tendsto trajExt atTop (𝓝 0) :=
  (extinction_isGloballyStable zero_le_one two_pos one_le_two).2 trajExt isSolution_trajExt
    (by norm_num [trajExt])

example {t : ℝ} (ht : 0 ≤ t) : trajExt t ≤ 1 := by
  have h := isSolution_trajExt.le_initial zero_le_one one_le_two
    (by norm_num [trajExt]) ht
  norm_num [trajExt] at h ⊢
  exact h

example : IsGloballyStable 1 2 0 (Icc 0 1) :=
  extinction_isGloballyStable zero_le_one two_pos one_le_two

/-! ### Non-vacuity of the solution and uniqueness hypotheses -/

example : IsSolution 2 1 (fun _ => 1 / 2) := by
  have h := isSolution_const_persistenceEq (c := 2) (e := 1) two_ne_zero
  simpa [persistenceEq_two_one] using h

example : IsSolution 3 5 (fun _ => 0) := isSolution_const_zero 3 5

/-- `traj` is not the constant equilibrium of `c = 2`, `e = 1`: it starts at `1/4`, not `1/2`. -/
example : traj ≠ fun _ => 1 / 2 := fun h => by
  have := congrFun h 0
  rw [traj_zero] at this
  norm_num at this

/-! ### The `c = 0` boundary -/

/-- At `c = 0` Lean's division gives `p* = 1`, but `1` is not an equilibrium of `p' = -p`, so the
results about `p*` need `c ≠ 0`. -/
example : persistenceEq 0 1 = 1 ∧ balance 0 1 1 ≠ 0 := by norm_num [persistenceEq, balance]

end MathlibExtTest.Biology.Ecology.LevinsMetapopulation
