/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.SaturableEliminationBoundary
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Tests for the monotone approach and the critical rate in saturable elimination.

Witnesses are built from the definitions, not from the theorems under test:

* `Vmax = 2`, `Km = 1`, `R = 1` has the equilibrium `c = 1` (`mmRate 2 1 1 = 1`).
* The constant `1` solves that equation (the equilibrium case).
* `belowSol` and `aboveSol`, non-constant solutions with `belowSol 0 = 0 < 1 = c` and
  `aboveSol 0 = 2 > c`, from the merged global Picard theorem
  `ode_global_exists_of_global_lipschitz` applied to the field clamped at `C = 0`, plus a direct
  barrier showing they stay nonnegative.
* `crit t = √(1 + 4 t) - 1` solves the critical equation `C' = 2 - mmRate 2 1 C` (`R = Vmax = 2`),
  checked by differentiating the square root directly. -/

open Real Set Filter Topology

namespace MathlibExtTest.Biology.Biophysics.SaturableEliminationBoundary

open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate)
open MathlibExt.Biology.Biophysics.SaturableEliminationBoundary

/-! ### Equilibria, from the definition of `mmRate` -/

/-- `Vmax = 2`, `Km = 1`, `R = 1`: the equilibrium is `c = R Km / (Vmax - R) = 1`. -/
example : mmRate 2 1 1 = 1 := by norm_num [mmRate]

/-- Near the critical rate the equilibrium is large: `R = 19/10` gives `c = 19`. -/
example : mmRate 2 1 19 = 19 / 10 := by norm_num [mmRate]

/-- `R = 199/100` gives `c = 199`: the equilibrium grows like `1 / (Vmax - R)`. -/
example : mmRate 2 1 199 = 199 / 100 := by norm_num [mmRate]

/-- The equilibrium forces `R < Vmax`. -/
example : (1 : ℝ) < 2 := lt_of_mmRate_eq (Vmax := 2) (Km := 1) (c := 1) two_pos one_pos zero_le_one
  (by norm_num [mmRate])

/-- The blow-up theorem at level `M = 100`, instantiated. -/
example : ∀ᶠ R in 𝓝[<] (2 : ℝ), ∀ c, 0 ≤ c → mmRate 2 1 c = R → 100 < c :=
  eventually_lt_of_mmRate_eq two_pos one_pos 100

/-! ### Equilibrium witness: the constant solution -/

lemma const_solves : ∀ t : ℝ, 0 ≤ t →
    HasDerivAt (fun _ ↦ (1 : ℝ)) (1 - mmRate 2 1 ((fun _ ↦ (1 : ℝ)) t)) t := by
  intro t _
  have : (1 : ℝ) - mmRate 2 1 1 = 0 := by norm_num [mmRate]
  simpa [this] using hasDerivAt_const t (1 : ℝ)

example : ∀ t : ℝ, 0 ≤ t → (fun _ ↦ (1 : ℝ)) t = 1 := fun _ ht ↦
  eq_of_initial_eq const_solves two_pos one_pos zero_le_one (by norm_num [mmRate]) rfl ht

example : MonotoneOn (fun _ : ℝ ↦ (1 : ℝ)) (Ici 0) :=
  monotoneOn_of_initial_le const_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    zero_le_one le_rfl

/-! ### A non-constant solution below the equilibrium -/

/-- The field `1 - mmRate 2 1 C`, clamped at `C = 0`. -/
noncomputable def clampedField (_ : ℝ) (y : ℝ) : ℝ := 1 - mmRate 2 1 (max y 0)

lemma clampedField_lipschitz (t : ℝ) : LipschitzWith 2 (clampedField t) := by
  refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
  have hy := le_max_right y 0
  have hz := le_max_right z 0
  have hm : |max y 0 - max z 0| ≤ |y - z| := abs_max_sub_max_le_abs y z 0
  simp only [clampedField, mmRate, Real.dist_eq, NNReal.coe_ofNat]
  have hkey : 1 - 2 * max y 0 / (1 + max y 0) - (1 - 2 * max z 0 / (1 + max z 0)) =
      -(2 * (max y 0 - max z 0) / ((1 + max y 0) * (1 + max z 0))) := by
    field_simp
    ring
  rw [hkey, abs_neg, abs_div, abs_mul, abs_two,
    abs_of_pos (by positivity : (0 : ℝ) < (1 + max y 0) * (1 + max z 0)),
    div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg (y - z))
    (by positivity : (0 : ℝ) ≤ max y 0 + max z 0 + max y 0 * max z 0)]

lemma clampedField_continuous : Continuous (Function.uncurry clampedField) := by
  unfold clampedField mmRate
  refine continuous_const.sub (Continuous.div (continuous_const.mul
    (continuous_snd.max continuous_const)) (continuous_const.add
    (continuous_snd.max continuous_const)) fun p ↦ by
      have := le_max_right p.2 0
      positivity)

/-- Direct barrier at `0` for any solution of the clamped equation starting at `D 0 ≥ 0`:
below `0` the clamped field equals `1 > 0`. -/
lemma nonneg_of_clamped {D : ℝ → ℝ} (hD : ∀ t, HasDerivAt D (clampedField t (D t)) t)
    (h0 : 0 ≤ D 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ D t := by
  have key : ∀ ε, 0 < ε → -D t ≤ ε := fun ε hε ↦
    image_le_of_deriv_right_lt_deriv_boundary (f := fun s ↦ -D s)
      (f' := fun s ↦ -clampedField s (D s)) (a := 0) (b := t) (B := fun _ ↦ ε)
      (B' := fun _ ↦ 0) (fun x _ ↦ (hD x).fun_neg.continuousAt.continuousWithinAt)
      (fun x _ ↦ (hD x).fun_neg.hasDerivWithinAt) (by linarith)
      (fun x ↦ hasDerivAt_const x _)
      (fun x _ hx ↦ by
        have : max (D x) 0 = 0 := max_eq_right (by linarith)
        simp [clampedField, this, mmRate])
      ⟨ht, le_rfl⟩
  have := le_of_forall_pos_le_add fun ε hε ↦ (show -D t ≤ 0 + ε by simpa using key ε hε)
  linarith

/-- The global solution of the clamped equation with `belowSol 0 = 0`. -/
noncomputable def belowSol : ℝ → ℝ :=
  (MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    clampedField 0 0 2 clampedField_continuous clampedField_lipschitz).exists.choose

lemma belowSol_zero : belowSol 0 = 0 :=
  (MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    clampedField 0 0 2 clampedField_continuous clampedField_lipschitz).exists.choose_spec.1

lemma hasDerivAt_belowSol (t : ℝ) : HasDerivAt belowSol (clampedField t (belowSol t)) t :=
  (MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    clampedField 0 0 2 clampedField_continuous clampedField_lipschitz).exists.choose_spec.2 t

lemma belowSol_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ belowSol t :=
  nonneg_of_clamped hasDerivAt_belowSol (by simp [belowSol_zero]) ht

/-- `belowSol` solves the unclamped equation `C' = 1 - mmRate 2 1 C` on `[0, ∞)`. -/
lemma belowSol_solves : ∀ t : ℝ, 0 ≤ t → HasDerivAt belowSol (1 - mmRate 2 1 (belowSol t)) t :=
    fun t ht ↦ by
    simpa [clampedField, max_eq_left (belowSol_nonneg ht)] using hasDerivAt_belowSol t

/-- `belowSol` is genuinely non-constant: its derivative at `0` is `1`, computed from the field. -/
example : HasDerivAt belowSol 1 0 := by
  simpa [belowSol_zero, mmRate] using belowSol_solves 0 le_rfl

/-- Strictly monotone approach from below, on a non-constant solution. -/
example : StrictMonoOn belowSol (Ici 0) :=
  strictMonoOn_of_initial_lt belowSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by simp [belowSol_zero]) (by simp [belowSol_zero])

/-- The equilibrium `1` is never reached. -/
example {t : ℝ} (ht : 0 ≤ t) : belowSol t < 1 :=
  lt_of_initial_lt belowSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by simp [belowSol_zero]) (by simp [belowSol_zero]) ht

/-- Explicit gap: `1 - belowSol t ≥ e^{-t}` (`λ = (2 - 1)/(1 + 0) = 1`). -/
example {t : ℝ} (ht : 0 ≤ t) : exp (-t) ≤ 1 - belowSol t := by
  have := mul_exp_le_sub_of_initial_le belowSol_solves two_pos one_pos zero_le_one
    (by norm_num [mmRate]) (by simp [belowSol_zero]) (by simp [belowSol_zero]) ht
  have h : -((2 - 1) / (1 + belowSol 0)) * t = -t := by rw [belowSol_zero]; ring
  rwa [h, belowSol_zero, _root_.sub_zero, one_mul] at this

/-- Invariance of the region below the equilibrium, on `belowSol`. -/
example {t : ℝ} (ht : 0 ≤ t) : belowSol t ≤ 1 :=
  le_of_initial_le belowSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by simp [belowSol_zero]) ht

/-- `belowSol` never drops below its initial value. -/
example {t : ℝ} (ht : 0 ≤ t) : belowSol 0 ≤ belowSol t :=
  initial_le_of_initial_le belowSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by simp [belowSol_zero]) (by simp [belowSol_zero]) ht

/-! ### A non-constant solution above the equilibrium -/

/-- The global solution of the clamped equation with `aboveSol 0 = 2`. -/
noncomputable def aboveSol : ℝ → ℝ :=
  (MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    clampedField 0 2 2 clampedField_continuous clampedField_lipschitz).exists.choose

lemma aboveSol_zero : aboveSol 0 = 2 :=
  (MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    clampedField 0 2 2 clampedField_continuous clampedField_lipschitz).exists.choose_spec.1

lemma hasDerivAt_aboveSol (t : ℝ) : HasDerivAt aboveSol (clampedField t (aboveSol t)) t :=
  (MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    clampedField 0 2 2 clampedField_continuous clampedField_lipschitz).exists.choose_spec.2 t

/-- `aboveSol` solves the unclamped equation `C' = 1 - mmRate 2 1 C` on `[0, ∞)`. -/
lemma aboveSol_solves : ∀ t : ℝ, 0 ≤ t → HasDerivAt aboveSol (1 - mmRate 2 1 (aboveSol t)) t :=
    fun t ht ↦ by
    simpa [clampedField, max_eq_left (nonneg_of_clamped hasDerivAt_aboveSol
      (by norm_num [aboveSol_zero]) ht)] using hasDerivAt_aboveSol t

/-- `aboveSol` is non-constant: its derivative at `0` is `1 - 4/3 = -1/3`, from the field. -/
example : HasDerivAt aboveSol (-1 / 3) 0 := by
  have h := aboveSol_solves 0 le_rfl
  rw [aboveSol_zero] at h
  convert h using 1
  norm_num [mmRate]

/-- Invariance of the region above the equilibrium. -/
example {t : ℝ} (ht : 0 ≤ t) : 1 ≤ aboveSol t :=
  le_of_le_initial aboveSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by norm_num [aboveSol_zero]) ht

/-- `aboveSol` never exceeds its initial value. -/
example {t : ℝ} (ht : 0 ≤ t) : aboveSol t ≤ aboveSol 0 :=
  le_initial_of_le_initial aboveSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by norm_num [aboveSol_zero]) ht

/-- Monotone approach from above. -/
example : AntitoneOn aboveSol (Ici 0) :=
  antitoneOn_of_le_initial aboveSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by norm_num [aboveSol_zero])

/-- Strictly monotone approach from above. -/
example : StrictAntiOn aboveSol (Ici 0) :=
  strictAntiOn_of_lt_initial aboveSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by norm_num [aboveSol_zero])

/-- The equilibrium `1` is never reached from above. -/
example {t : ℝ} (ht : 0 ≤ t) : 1 < aboveSol t :=
  lt_of_lt_initial aboveSol_solves two_pos one_pos zero_le_one (by norm_num [mmRate])
    (by norm_num [aboveSol_zero]) ht

/-- Explicit gap from above: `aboveSol t - 1 ≥ e^{-t/2}` (`λ = (2 - 1)/(1 + 1) = 1/2`). -/
example {t : ℝ} (ht : 0 ≤ t) : exp (-(t / 2)) ≤ aboveSol t - 1 := by
  have := mul_exp_le_sub_of_le_initial aboveSol_solves two_pos one_pos zero_le_one
    (by norm_num [mmRate]) (by norm_num [aboveSol_zero]) ht
  have h : -(((2 : ℝ) - 1) / (1 + 1)) * t = -(t / 2) := by ring
  rwa [h, aboveSol_zero, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] at this

/-! ### The critical rate `R = Vmax = 2`, `Km = 1`, `C(0) = 0` -/

/-- Explicit critical solution `√(1 + 4 t) - 1`. -/
noncomputable def crit (t : ℝ) : ℝ := √(1 + 4 * t) - 1

lemma crit_solves : ∀ t : ℝ, 0 ≤ t → HasDerivAt crit (2 - mmRate 2 1 (crit t)) t := by
  intro t ht
  have hpos : 0 < 1 + 4 * t := by linarith
  have hs : 0 < √(1 + 4 * t) := Real.sqrt_pos.2 hpos
  have hd := (((hasDerivAt_id' t).const_mul 4).const_add 1).sqrt hpos.ne' |>.sub_const 1
  show HasDerivAt (fun s ↦ √(1 + 4 * s) - 1) _ t
  convert hd using 1
  simp only [crit, mmRate]
  have h1 : (1 : ℝ) + (√(1 + 4 * t) - 1) = √(1 + 4 * t) := by ring
  rw [h1]
  field_simp
  ring

example : crit 0 = 0 := by simp [crit]

/-- The exact critical integral at sample time `t = 2`: `(1 + C(2))² = 1 + 2·2·1·2 = 9`. -/
example : (1 + crit 2) ^ 2 = 9 := by
  have := sq_add_critical crit_solves two_pos one_pos (by simp [crit]) (by norm_num : (0 : ℝ) ≤ 2)
  rw [this]
  norm_num [crit]

/-- Independent check of the same value from the definition: `crit 2 = √9 - 1 = 2`. -/
example : crit 2 = 2 := by
  have : √(9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [crit, this]

/-- At the critical rate the solution never drops below its initial value. -/
example {t : ℝ} (ht : 0 ≤ t) : crit 0 ≤ crit t :=
  initial_le_critical crit_solves two_pos one_pos (by simp [crit]) ht

/-- The closed form instantiated on `crit`, cross-checked against the definition of `crit`. -/
example {t : ℝ} (ht : 0 ≤ t) :
    crit t = √((1 + crit 0) ^ 2 + 2 * 2 * 1 * t) - 1 ∧
      √((1 + crit 0) ^ 2 + 2 * 2 * 1 * t) - 1 = √(1 + 4 * t) - 1 :=
  ⟨eq_sqrt_critical crit_solves two_pos one_pos (by simp [crit]) ht, by norm_num [crit]⟩

example : StrictMonoOn crit (Ici 0) :=
  strictMonoOn_critical crit_solves two_pos one_pos (by simp [crit])

/-- No steady state at the critical rate. -/
example : Tendsto crit atTop atTop :=
  tendsto_atTop_critical crit_solves two_pos one_pos (by simp [crit])

/-- Square-root growth with constant `√(2 Vmax Km) = √4 = 2`. -/
example : Tendsto (fun t ↦ crit t / √t) atTop (𝓝 2) := by
  have h := tendsto_div_sqrt_critical crit_solves two_pos one_pos (by simp [crit])
  have : √(2 * 2 * 1 : ℝ) = 2 := by
    rw [show (2 * 2 * 1 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [this] at h

/-- Sublinear growth. -/
example : Tendsto (fun t ↦ crit t / t) atTop (𝓝 0) :=
  tendsto_div_critical crit_solves two_pos one_pos (by simp [crit])

/-- Bracketing at `t = 2`: `√8 - 1 ≤ crit 2 ≤ 0 + √8`. -/
example : √(2 * 2 * 1 * 2) - 1 ≤ crit 2 ∧ crit 2 ≤ crit 0 + √(2 * 2 * 1 * 2) :=
  ⟨sqrt_sub_le_critical crit_solves two_pos one_pos (by simp [crit]) (by norm_num),
    le_add_sqrt_critical crit_solves two_pos one_pos (by simp [crit]) (by norm_num)⟩

end MathlibExtTest.Biology.Biophysics.SaturableEliminationBoundary
