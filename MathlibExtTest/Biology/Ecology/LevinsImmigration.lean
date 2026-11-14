/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Ecology.LevinsImmigration
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for the Levins model with immigration

Values are computed from the definitions, not through the theorems under test:

* The equilibrium `p̂` in four regimes: `c = e` (`c = e = 1`, `m = 1/2`, `p̂ = 1/2`), `c < e`
  (`c = 1`, `e = 2`, `m = 3/2`, `p̂ = 1/2`), `c = 0` (`e = m = 1`, `p̂ = m / (e + m) = 1/2`) and the
  `e = 0` boundary (`c = m = 1`, `p̂ = 1`).
* At `c = e = 1` without immigration the only equilibrium in `[0, ∞)` is extinction; with
  `m = 1/2` the trajectory `p(t) = 1/2 - 3 / (4 e^{3t/2} + 2)` from an empty landscape solves the
  equation (derivative computed by hand), is positive for `t > 0`, and tends to `1/2`.
* At `m = 0` the formula collapses to `0` and the balance has two equilibria in `[0, 1]` when
  `c > e`, so the hypothesis `m > 0` is needed for uniqueness; as `m ↓ 0` the equilibrium tends to
  the Levins persistence equilibrium instead.
-/

open Real Filter Set
open scoped Topology

namespace MathlibExtTest.Biology.Ecology.LevinsImmigration

open MathlibExt.Biology.Ecology
open MathlibExt.Biology.Ecology.LevinsImmigration

/-! ### Equilibria from the definition -/

/-- `c = e = 1`, `m = 1/2`: `disc = 9/4`, `p̂ = 1 / (1/2 + 3/2) = 1/2`. -/
theorem immigrationEq_one_one : immigrationEq 1 1 (1 / 2) = 1 / 2 := by
  have hd : disc 1 1 (1 / 2) = (3 / 2) ^ 2 := by norm_num [disc]
  rw [immigrationEq, hd, Real.sqrt_sq (by norm_num)]
  norm_num

/-- `c = 1 < e = 2`, `m = 3/2`: `disc = 49/4`, `p̂ = 3 / 6 = 1/2`. -/
theorem immigrationEq_one_two : immigrationEq 1 2 (3 / 2) = 1 / 2 := by
  have hd : disc 1 2 (3 / 2) = (7 / 2) ^ 2 := by norm_num [disc]
  rw [immigrationEq, hd, Real.sqrt_sq (by norm_num)]
  norm_num

/-- `c = 0`: `p̂ = m / (e + m)`. -/
theorem immigrationEq_zero_one : immigrationEq 0 1 1 = 1 / 2 := by
  have hd : disc 0 1 1 = 2 ^ 2 := by norm_num [disc]
  rw [immigrationEq, hd, Real.sqrt_sq (by norm_num)]
  norm_num

/-- `e = 0`: the landscape fills up, `p̂ = 1`. -/
theorem immigrationEq_one_zero : immigrationEq 1 0 1 = 1 := by
  have hd : disc 1 0 1 = 2 ^ 2 := by norm_num [disc]
  rw [immigrationEq, hd, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The computed values are equilibria, checked on the balance itself. -/
example : balance 1 1 (1 / 2) (1 / 2) = 0 := by norm_num [balance]

example : balance 1 2 (3 / 2) (1 / 2) = 0 := by norm_num [balance]

example : balance 0 1 1 (1 / 2) = 0 := by norm_num [balance]

example : balance 1 0 1 1 = 0 := by norm_num [balance]

/-- Extinction is not an equilibrium: `f(0) = m`. -/
example : balance 1 1 (1 / 2) 0 = 1 / 2 := by norm_num [balance]

/-- Agreement with the theorems: the uniqueness characterization picks out the computed value. -/
example : balance 1 1 (1 / 2) (immigrationEq 1 1 (1 / 2)) = 0 :=
  balance_immigrationEq zero_le_one zero_le_one (by norm_num)

example : (1 / 2 : ℝ) = immigrationEq 1 1 (1 / 2) :=
  (balance_eq_zero_iff zero_le_one zero_le_one (by norm_num) (by norm_num)).1
    (by norm_num [balance])

/-- The quadratic-formula form at `c = 1`, `e = 2`, `m = 3/2`: `(-5/2 + 7/2) / 2 = 1/2`. -/
example : (1 - 2 - 3 / 2 + √(disc 1 2 (3 / 2))) / (2 * 1) = (1 / 2 : ℝ) := by
  have hd : disc 1 2 (3 / 2) = (7 / 2) ^ 2 := by norm_num [disc]
  rw [hd, Real.sqrt_sq (by norm_num)]
  norm_num

example : immigrationEq 1 0 1 = 1 :=
  (immigrationEq_eq_one_iff zero_le_one le_rfl one_pos).2 rfl

example : immigrationEq 1 2 (3 / 2) < 1 :=
  immigrationEq_lt_one zero_le_one two_pos (by norm_num)

/-- The linearization at `p̂ = 1/2` for `c = e = 1`, `m = 1/2`, computed from the derivative of
`-p² - p/2 + 1/2`: `-2 · 1/2 - 1/2 = -3/2`. -/
example : HasDerivAt (balance 1 1 (1 / 2)) (-(3 / 2)) (1 / 2) := by
  have h := hasDerivAt_balance (1 : ℝ) 1 (1 / 2) (1 / 2)
  norm_num at h
  exact h

example : rate 1 1 (1 / 2) = 3 / 2 := by norm_num [rate, immigrationEq_one_one]

/-! ### Without immigration: extinction is the only equilibrium (`c = e = 1`) -/

/-- At `m = 0`, `c = e = 1`, the balance `-p²` vanishes on `[0, ∞)` only at `0`. -/
example (p : ℝ) (h : LevinsMetapopulation.balance 1 1 p = 0) : p = 0 := by
  simp only [LevinsMetapopulation.balance] at h
  nlinarith [sq_nonneg p]

example (p : ℝ) : balance 1 1 0 p = LevinsMetapopulation.balance 1 1 p :=
  balance_zero_right 1 1 p

/-! ### With immigration: a trajectory from an empty landscape (`c = e = 1`, `m = 1/2`) -/

/-- `p(t) = 1/2 - 3 / (4 e^{3t/2} + 2)`, the solution from `p(0) = 0`. -/
noncomputable def traj (t : ℝ) : ℝ := 1 / 2 - 3 / (4 * exp (3 / 2 * t) + 2)

theorem traj_zero : traj 0 = 0 := by norm_num [traj]

/-- `traj` solves `p' = p (1 - p) - p + (1 - p) / 2` (derivative computed directly). -/
theorem isSolution_traj : IsSolution 1 1 (1 / 2) traj := by
  refine ⟨fun t _ => ?_⟩
  have hE : HasDerivAt (fun s => exp (3 / 2 * s)) (exp (3 / 2 * t) * (3 / 2 * 1)) t :=
    ((hasDerivAt_id' t).const_mul (3 / 2)).exp
  have hD := (hE.const_mul 4).add_const 2
  have hD0 : 4 * exp (3 / 2 * t) + 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_const t (3 : ℝ)).div hD hD0).const_sub (1 / 2)
  refine h.congr_deriv ?_
  simp only [balance, traj]
  field_simp
  ring

/-- An empty landscape is colonized at once: `traj t > 0` for `t > 0`, computed directly. -/
example {t : ℝ} (ht : 0 < t) : 0 < traj t := by
  have hE : 1 < exp (3 / 2 * t) := one_lt_exp_iff.2 (by positivity)
  unfold traj
  rw [sub_pos, div_lt_iff₀ (by positivity)]
  linarith

/-- The same positivity from `IsSolution.pos`. -/
example {t : ℝ} (ht : 0 < t) : 0 < traj t :=
  isSolution_traj.pos (by norm_num) (by rw [traj_zero]) ht

/-- `traj → 1/2`, computed directly from `e^{3t/2} → ∞`. -/
theorem tendsto_traj : Tendsto traj atTop (𝓝 (1 / 2)) := by
  have hE : Tendsto (fun t : ℝ => exp (3 / 2 * t)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have hD : Tendsto (fun t : ℝ => 4 * exp (3 / 2 * t) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 (hE.const_mul_atTop (by norm_num))
  have h := (tendsto_const_nhds (x := (3 : ℝ))).div_atTop hD
  have h2 := h.const_sub (1 / 2 : ℝ)
  rw [sub_zero] at h2
  exact h2

/-- The direct limit is the computed equilibrium; for `m = 0` the same rates go extinct. -/
example : Tendsto traj atTop (𝓝 (immigrationEq 1 1 (1 / 2))) := by
  rw [immigrationEq_one_one]; exact tendsto_traj

/-- The global-stability theorem applies to `traj` and gives the same limit. -/
example : Tendsto traj atTop (𝓝 (immigrationEq 1 1 (1 / 2))) :=
  (isGloballyStable zero_le_one zero_le_one (by norm_num)).2 traj isSolution_traj
    (by rw [traj_zero]; exact mem_Ici.2 le_rfl)

/-- `traj` stays in `[0, 1]`, from the invariance theorem. -/
example {t : ℝ} (ht : 0 ≤ t) : traj t ∈ Icc 0 1 :=
  isSolution_traj.mem_Icc zero_le_one zero_le_one (by norm_num) (by rw [traj_zero]; simp) ht

/-- Exponential rate `m / p̂ = 1`: `|p(t) - 1/2| ≤ e^{-t} / 2`. -/
example {t : ℝ} (ht : 0 ≤ t) : |traj t - 1 / 2| ≤ 1 / 2 * exp (-(1 * t)) := by
  have h := isSolution_traj.abs_sub_le_exp zero_le_one zero_le_one (by norm_num)
    (by rw [traj_zero]) ht
  rw [immigrationEq_one_one, traj_zero] at h
  norm_num at h ⊢
  exact h

/-- **Persistence under propagule rain at `c = e = 1`.** -/
example : LevinsMetapopulation.IsGloballyStable 1 1 0 (Icc 0 1) ∧
    0 < immigrationEq 1 1 (1 / 2) ∧
      IsGloballyStable 1 1 (1 / 2) (immigrationEq 1 1 (1 / 2)) (Ici 0) :=
  propagule_rain_persistence zero_le_one one_pos le_rfl (by norm_num)

/-- The explicit solution exists from `p₀ = 0`, and starts there. -/
example : solution 1 1 (1 / 2) 0 0 = 0 :=
  solution_zero zero_le_one zero_le_one (by norm_num) 0

/-! ### The hypothesis `m > 0` -/

/-- At `m = 0` the formula collapses to `0`. -/
example : immigrationEq 2 1 0 = 0 := by simp [immigrationEq]

/-- At `m = 0`, `c = 2 > e = 1`, there are two equilibria in `[0, 1]`: uniqueness needs `m > 0`. -/
example : balance 2 1 0 0 = 0 ∧ balance 2 1 0 (1 / 2) = 0 := by
  constructor <;> norm_num [balance]

/-- As `m ↓ 0` with `c = 2 > e = 1`, `p̂` tends to the Levins persistence equilibrium `1/2`. -/
example : Tendsto (fun m => immigrationEq 2 1 m) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h := tendsto_immigrationEq_zero (c := 2) (e := 1) two_pos zero_le_one
  have hv : max (LevinsMetapopulation.persistenceEq 2 1) 0 = 1 / 2 := by
    norm_num [LevinsMetapopulation.persistenceEq]
  rwa [hv] at h

/-- As `m ↓ 0` with `c = 1 < e = 2`, `p̂` tends to extinction. -/
example : Tendsto (fun m => immigrationEq 1 2 m) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_immigrationEq_zero (c := 1) (e := 2) one_pos zero_le_two
  have hv : max (LevinsMetapopulation.persistenceEq 1 2) 0 = 0 := by
    norm_num [LevinsMetapopulation.persistenceEq]
  rwa [hv] at h

end MathlibExtTest.Biology.Ecology.LevinsImmigration
