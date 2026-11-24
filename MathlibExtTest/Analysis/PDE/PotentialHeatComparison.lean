/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.PotentialHeatComparison
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Set Real
open MathlibExt.Analysis.PDE.HeatWholeLine

-- This negative field has positive heat residual. Only the positive-set premise applies.
example {ν T : ℝ} (hν : 0 ≤ ν) (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
    -exp (-t) ≤ 0 := by
  exact nonpos_of_heat_subsolution_on_pos_of_le_exp
    (u := fun t _ => -exp (-t)) (ut := fun t _ => exp (-t)) hν
    (by fun_prop) (fun _ _ _ => by fun_prop)
    (fun t _ _ => by
      simpa using! (((hasDerivAt_id' t).neg.exp).neg.hasDerivWithinAt))
    (fun t _ _ hp => (not_lt_of_ge (neg_nonpos.mpr (exp_pos _).le) hp).elim)
    ⟨0, 0, le_rfl, le_rfl, fun t _ _ => by simp; positivity⟩
    (fun _ => by simp) t ht x


-- This potential is bounded above but unbounded below; no absolute bound is required.
example {ν T : ℝ} (hν : 0 ≤ ν) : ∀ t ∈ Icc 0 T, ∀ _x : ℝ, -exp (-t) ≤ 0 := by
  apply nonpos_of_potential_subsolution (u := fun t _ => -exp (-t))
    (ut := fun t _ => exp (-t)) (q := fun _ x => -1-x^2) (K := -1) hν
    (by fun_prop) (fun _ _ _ => by fun_prop)
    (fun t _ _ => by simpa using! ((hasDerivAt_id' t).neg.exp).neg)
  · intro t _ x
    simp only [iteratedDeriv_const, OfNat.ofNat_ne_zero, ↓reduceIte, mul_zero, sub_zero]
    nlinarith [sq_nonneg x, exp_pos (-t), mul_nonneg (sq_nonneg x) (exp_pos (-t)).le]
  · intro _ _ x; nlinarith [sq_nonneg x]
  · apply HasExpGrowthOnStrip.of_bounded
    refine ⟨1, fun t ht _ => ?_⟩
    rw [abs_neg, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
  · intro _; simp

-- No finite left derivative exists at the terminal time for this square-root corner.
-- The theorem nevertheless controls the whole closed strip from interior derivatives.
example {ν : ℝ} (hν : 0 ≤ ν) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ _x : ℝ, sqrt (1-t)-1 ≤ 0 := by
  apply nonpos_of_potential_subsolution (u := fun t _ => sqrt (1-t)-1)
    (ut := fun t _ => -1 / (2*sqrt (1-t))) (q := fun _ _ => 0) (K := 0) hν
    (by fun_prop) (fun _ _ _ => by fun_prop)
    (fun t ht _ => by
      simpa using! (((hasDerivAt_id' t).const_sub 1).sqrt (by linarith [ht.2] : 1-t ≠ 0)).sub_const 1)
  · intro t _ x
    simp only [iteratedDeriv_const, OfNat.ofNat_ne_zero, ↓reduceIte, mul_zero, sub_zero, zero_mul]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  · intro _ _ _; rfl
  · apply HasExpGrowthOnStrip.of_bounded
    refine ⟨1, fun t ht _ => ?_⟩
    have hs : sqrt (1-t) ≤ 1 := (sqrt_le_one).mpr (by linarith [ht.1])
    exact abs_le.mpr ⟨by linarith [sqrt_nonneg (1-t)], by linarith⟩
  · intro _; norm_num

private theorem linear_time_growth (T : ℝ) : HasExpGrowthOnStrip (fun t _ => t) T :=
  HasExpGrowthOnStrip.of_bounded ⟨max T 0, fun t ht _ => by
    rw [abs_of_nonneg ht.1]; exact ht.2.trans (le_max_left _ _)⟩

-- Ordered, unequal, nonzero sources with a negative potential; zero diffusivity is allowed.
example (T : ℝ) : ∀ t ∈ Icc 0 T, ∀ _x : ℝ, -t ≤ t := by
  have hn : HasExpGrowthOnStrip (fun t (_ : ℝ) => -t) T := by
    simpa only [HasExpGrowthOnStrip, abs_neg] using linear_time_growth T
  exact le_of_potential_residual_le (u := fun t _ => -t) (v := fun t _ => t)
    (ut := fun _ _ => -1) (vt := fun _ _ => 1) (q := fun _ _ => -2) (ν := 0) (K := -2)
    (by norm_num) (by fun_prop) (by fun_prop) (fun _ _ _ => by fun_prop)
    (fun _ _ _ => by fun_prop) (fun t _ _ => by simpa using! (hasDerivAt_id' t).neg)
    (fun t _ _ => hasDerivAt_id' t)
    (fun t ht _ => by simp only [zero_mul, sub_zero]; nlinarith [ht.1]) (by intros; rfl)
    hn (linear_time_growth T) (by simp)

-- Common nonzero source and positive potential identify any signed growth-class competitor.
example {u ut : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 ≤ ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioo 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => u s x) (ut t x) t)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x - 3*u t x = 1-3*t)
    (hg : HasExpGrowthOnStrip u T) (h₀ : ∀ x, u 0 x = 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x = t := by
  exact eq_of_potential_equation (v := fun t _ => t) (vt := fun _ _ => 1)
    (q := fun _ _ => 3) (K := 3) (f := fun t _ => 1-3*t) hν hc (by fun_prop) hx
    (fun _ _ _ => by fun_prop) ht (fun t _ _ => hasDerivAt_id' t) hpde
    (by intros; simp [iteratedDeriv_const]) (by intros; rfl) hg (linear_time_growth T) h₀

-- At zero horizon, no spatial or temporal regularity is imposed even on a rough initial field.
example (ν : ℝ) (hν : 0 ≤ ν) (x : ℝ) : -|sin x| ≤ 0 := by
  exact nonpos_of_potential_subsolution (u := fun _ x => -|sin x|) (ut := fun _ _ => 0)
    (q := fun _ x => x^2) (K := 0) (T := 0) hν (by fun_prop)
    (by simp) (by simp) (by simp) (by simp)
    (HasExpGrowthOnStrip.of_bounded ⟨1, fun _ _ x => by simpa only [abs_neg, abs_abs] using abs_sin_le_one x⟩)
    (fun _ => neg_nonpos.mpr (abs_nonneg _)) 0 ⟨le_rfl,le_rfl⟩ x

open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

private theorem exp_profile_growth (T : ℝ) :
    HasExpGrowthOnStrip (fun t x => exp (5*t+x)) T := by
  refine ⟨exp (5*T),1,(exp_pos _).le,by norm_num,fun t ht x => ?_⟩
  rw [abs_of_pos (exp_pos _), one_mul, ← exp_add]
  exact exp_le_exp.mpr (by linarith [ht.2,le_abs_self x])

private theorem exp_profile_second (t x : ℝ) :
    iteratedDeriv 2 (fun y => exp (5*t+y)) x = exp (5*t+x) := by
  rw [iteratedDeriv_comp_const_add]
  simp [iteratedDeriv_eq_iterate, iter_deriv_exp]

-- Identify the actual construction with unbounded data, nonzero positive potential,
-- nonunit viscosity and a nonzero second spatial derivative.
example {T t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution 2 (fun _ _ => 3) exp t x = exp (5*t+x) := by
  symm
  apply eq_potentialHeatSolution_of_exp_growth (u := fun t x => exp (5*t+x))
    (ut := fun t x => 5*exp (5*t+x)) (by norm_num)
    (fun _ _ => contDiff_const)
    (fun k _ => by simp only [iteratedDeriv_const]; split_ifs <;> fun_prop)
    (fun k _ => ⟨3, fun _ _ _ => by simp only [iteratedDeriv_const]; split_ifs <;> norm_num⟩)
    continuous_exp (by simpa using HasExpGrowth.exp_linear 1)
    (by fun_prop) (fun _ _ _ => by fun_prop)
    (fun t _ x => by
      simpa only [mul_one, one_mul, mul_comm] using!
        (((hasDerivAt_id' t).const_mul 5).add_const x).exp)
    (fun t _ x => by rw [exp_profile_second]; ring)
    (exp_profile_growth T) (by simp) t ht x

private theorem signed_profile_growth (T : ℝ) :
    HasExpGrowthOnStrip (fun t x => exp (-t)*x) T := by
  refine ⟨1,1,by norm_num,by norm_num,fun t ht x => ?_⟩
  rw [abs_mul,abs_of_pos (exp_pos _),one_mul,one_mul]
  calc
    exp (-t)*|x| ≤ |x| := mul_le_of_le_one_left (abs_nonneg _)
      (exp_le_one_iff.mpr (neg_nonpos.mpr ht.1))
    _ ≤ exp |x| := by linarith [add_one_le_exp |x|]

-- Negative potential, sign-changing unbounded data and both time endpoints.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν (fun _ _ => -1) (fun x => x) t x = exp (-t)*x := by
  symm
  apply eq_potentialHeatSolution_of_exp_growth (u := fun t x => exp (-t)*x)
    (ut := fun t x => -exp (-t)*x) hν (fun _ _ => contDiff_const)
    (fun k _ => by simp only [iteratedDeriv_const]; split_ifs <;> fun_prop)
    (fun k _ => ⟨1, fun _ _ _ => by simp only [iteratedDeriv_const]; split_ifs <;> norm_num⟩)
    continuous_id ⟨1,1,by norm_num,by norm_num,fun x => by
      simp only [one_mul, id_eq]; linarith [add_one_le_exp |x|]⟩
    (by fun_prop) (fun _ _ _ => by fun_prop)
    (fun t _ x => by simpa using! (((hasDerivAt_id' t).neg.exp).mul_const x))
    (fun t _ x => by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_const_mul_id',
        deriv_const, mul_zero, zero_add]
      ring)
    (signed_profile_growth T) (by simp) t ht x

-- An arbitrary bounded-above potential may be discontinuous.
example {T : ℝ} : ∀ t ∈ Icc 0 T, ∀ _x : ℝ, -exp (-t) ≤ 0 := by
  apply nonpos_of_potential_subsolution (u := fun t _ => -exp (-t))
    (ut := fun t _ => exp (-t)) (q := fun _ x => if x ≤ 0 then -1 else -2)
    (K := -1) (ν := 3) (by norm_num) (by fun_prop) (fun _ _ _ => by fun_prop)
    (fun t _ _ => by simpa using! ((hasDerivAt_id' t).neg.exp).neg)
  · intro t _ x
    simp only [iteratedDeriv_const, OfNat.ofNat_ne_zero, ↓reduceIte, mul_zero, sub_zero]
    split_ifs <;> nlinarith [exp_pos (-t)]
  · intro _ _ x; split_ifs <;> norm_num
  · apply HasExpGrowthOnStrip.of_bounded
    refine ⟨1, fun t ht _ => ?_⟩
    rw [abs_neg, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
  · intro _; simp
