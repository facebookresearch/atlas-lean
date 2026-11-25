/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatWholeLine
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Filter Topology Real
open scoped ContDiff
open MathlibExt.Analysis.PDE.HeatWholeLine

-- The public maximum principle controls the final time as well as the open strip.
example {u ut : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hsub : ∀ t ∈ Ioc 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x ≤ 0)
    (hg : HasExpGrowthOnStrip u T) (h₀ : ∀ x, u 0 x ≤ 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ 0 :=
  nonpos_of_heat_subsolution hν hc hx ht hsub hg h₀

-- Growth constants are uniform on the strip, but may depend on its length.
example (T : ℝ) : HasExpGrowthOnStrip (fun t _ => t) T := by
  apply HasExpGrowthOnStrip.of_bounded
  exact ⟨max T 0, fun t ht _ => by rw [abs_of_nonneg ht.1]; exact ht.2.trans (le_max_left _ _)⟩

-- Different spatial exponential rates are accepted by the difference API.
example (T : ℝ) : HasExpGrowthOnStrip (fun _ x => exp x - exp (-2 * x)) T := by
  apply HasExpGrowthOnStrip.sub
  · refine ⟨1, 1, by norm_num, by norm_num, fun _ _ x => ?_⟩
    simpa only [abs_of_pos (exp_pos _), one_mul] using exp_le_exp.mpr (le_abs_self x)
  · refine ⟨1, 2, by norm_num, by norm_num, fun _ _ x => ?_⟩
    rw [abs_of_pos (exp_pos _), one_mul]
    apply exp_le_exp.mpr
    nlinarith [neg_abs_le x]

-- Ordered nonzero sources: -t is a subsolution relative to +t, for any diffusivity.
example {ν T : ℝ} (hν : 0 ≤ ν) : ∀ t ∈ Icc 0 T, ∀ _x : ℝ, -t ≤ t := by
  have hb : HasExpGrowthOnStrip (fun t (_ : ℝ) => t) T :=
    HasExpGrowthOnStrip.of_bounded ⟨max T 0, fun t ht _ => by
      rw [abs_of_nonneg ht.1]; exact ht.2.trans (le_max_left _ _)⟩
  have hn : HasExpGrowthOnStrip (fun t (_ : ℝ) => -t) T := by
    apply HasExpGrowthOnStrip.of_bounded
    refine ⟨max T 0, fun t ht _ => ?_⟩
    rw [abs_neg, abs_of_nonneg ht.1]
    exact ht.2.trans (le_max_left _ _)
  exact le_of_heat_residual_le (u := fun t _ => -t) (v := fun t _ => t)
    (ut := fun _ _ => -1) (vt := fun _ _ => 1) hν (by fun_prop) (by fun_prop)
    (by intros; fun_prop) (by intros; fun_prop)
    (fun t _ _ => (hasDerivAt_id' t).neg.hasDerivWithinAt)
    (fun t _ _ => (hasDerivAt_id' t).hasDerivWithinAt)
    (by intros; simp [iteratedDeriv_const]) hn hb (by simp)

-- Uniqueness with a nonzero source compares an arbitrary bounded solution with t.
example {u ut : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hpde : ∀ t ∈ Ioc 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x = 1)
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) (h₀ : ∀ x, u 0 x = 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x = t := by
  exact eq_of_heat_equation_of_bounded (v := fun t _ => t) (vt := fun _ _ => 1)
    (f := fun _ _ => 1) hν hc (by fun_prop) hx (by intros; fun_prop) ht
    (fun t _ _ => (hasDerivAt_id' t).hasDerivWithinAt) hpde
    (by intros; simp [iteratedDeriv_const]) hb
    ⟨max T 0, fun t ht _ => by rw [abs_of_nonneg ht.1]; exact ht.2.trans (le_max_left _ _)⟩ h₀

-- A one-sided bound allows a negative field of quadratic-exponential magnitude.
-- Zero diffusivity is legitimate: here the equation is u_t = 0.
example (T : ℝ) : ∀ t ∈ Icc 0 T, ∀ x : ℝ, -exp (x ^ 2) ≤ 0 := by
  exact nonpos_of_heat_subsolution_of_le_exp (u := fun _ x => -exp (x ^ 2))
    (ut := fun _ _ => 0) (ν := 0) (by norm_num) (by fun_prop)
    (by intros; fun_prop) (fun _ _ _ => (hasDerivAt_const _ _).hasDerivWithinAt)
    (by intros; simp)
    ⟨0, 0, le_rfl, le_rfl, fun _ _ x => by simp [le_of_lt (exp_pos _)]⟩
    (fun x => neg_nonpos.mpr (exp_pos _).le)

-- A bounded strict subsolution exercises the final-time endpoint at nonunit viscosity.
example : (fun (t : ℝ) (_ : ℝ) => -t) 2 17 ≤ 0 := by
  exact nonpos_of_heat_subsolution (u := fun t _ => -t) (ut := fun _ _ => -1) (ν := 3) (T := 2)
    (by norm_num) (by fun_prop) (by intros; fun_prop)
    (fun t _ _ => (hasDerivAt_id' t).neg.hasDerivWithinAt) (by intros; simp [iteratedDeriv_const])
    (HasExpGrowthOnStrip.of_bounded ⟨2, fun t ht _ => by
      rw [abs_neg, abs_of_nonneg ht.1]; exact ht.2⟩) (by simp) 2 (by constructor <;> norm_num) 17

-- Initial continuity cannot be replaced by an assigned value at t = 0.
-- This bounded field solves the positive-time PDE and has zero assigned initial values,
-- yet is nonzero later. It fails the closed-strip continuity hypothesis.
private noncomputable def jump (t : ℝ) (_x : ℝ) : ℝ := if t ≤ 0 then 0 else 1

example (x : ℝ) : jump 0 x = 0 := by simp [jump]

private theorem jump_regular {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => jump s x) 0 t ∧ iteratedDeriv 2 (jump t) x = 0 := by
  constructor
  · apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    simp [jump, not_le.mpr hs]
  · change iteratedDeriv 2 (fun _ => if t ≤ 0 then (0 : ℝ) else 1) x = 0
    simp [iteratedDeriv_const]

example : jump 1 0 ≠ jump 0 0 := by norm_num [jump]

example (T : ℝ) : HasExpGrowthOnStrip jump T := by
  apply HasExpGrowthOnStrip.of_bounded
  refine ⟨1, fun t _ x => ?_⟩
  unfold jump
  split_ifs <;> norm_num

example {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => jump s x) t = 3 * iteratedDeriv 2 (jump t) x := by
  rw [(jump_regular ht x).1.deriv, (jump_regular ht x).2, mul_zero]

example : ¬ ContinuousOn (Function.uncurry jump) (Icc 0 1 ×ˢ univ) := by
  intro hc
  have hg : HasExpGrowthOnStrip jump 1 := by
    apply HasExpGrowthOnStrip.of_bounded
    refine ⟨1, fun t _ x => ?_⟩
    unfold jump
    split_ifs <;> norm_num
  have h := nonpos_of_heat_subsolution (u := jump) (ut := fun _ _ => 0)
    (ν := 3) (by norm_num) hc (by intros; unfold jump; fun_prop)
    (fun t ht x => (jump_regular ht.1 x).1.hasDerivWithinAt)
    (fun t ht x => by rw [(jump_regular ht.1 x).2]; norm_num) hg (by simp [jump])
  have hh := h 1 (by constructor <;> norm_num) 0
  norm_num [jump] at hh

#print axioms MathlibExt.Analysis.PDE.HeatWholeLine.nonpos_of_heat_subsolution_of_le_exp
#print axioms MathlibExt.Analysis.PDE.HeatWholeLine.le_of_heat_residual_le
#print axioms MathlibExt.Analysis.PDE.HeatWholeLine.eq_of_heat_equation
