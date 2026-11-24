/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.ForcedBurgersBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open Set Real
open scoped ContDiff
open ColeHopf

-- The bound is a conclusion for the actual field, not an input assumption on it.
example {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T M A t : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀)
    (hM : 0 ≤ M) (hub : ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ C, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ C)
    (hA : 0 ≤ A) (hqb : ∀ s ∈ Icc 0 T, ∀ x, |deriv (q s) x| ≤ A)
    (ht : t ∈ Icc 0 T) (a x : ℝ) :
    |forcedBurgersSolution ν q u₀ a t x| ≤ M + 2 * ν * A * t :=
  abs_forcedBurgersSolution_le hν hT hu hM hub hq hb hA hqb ht a x

private theorem trig_jet_bound (k : ℕ) :
    (∀ x : ℝ, |iteratedDeriv k sin x| ≤ 1) ∧ (∀ x : ℝ, |iteratedDeriv k cos x| ≤ 1) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using And.intro abs_sin_le_one abs_cos_le_one
  | succ k ih =>
    constructor
    · simpa only [iteratedDeriv_add_one_sin] using ih.2
    · simpa only [iteratedDeriv_add_one_cos, Pi.neg_apply, abs_neg] using ih.1

private theorem sine_linear_frechet_bound (L : ℝ × ℝ →L[ℝ] ℝ) (n : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun z => sin (L z)) p‖ ≤ ‖L‖^n := by
  have h := L.iteratedFDeriv_comp_right (f := sin) (show ContDiff ℝ ∞ sin from by fun_prop)
    p (i := n) (by simp)
  change iteratedFDeriv ℝ n (fun z => sin (L z)) p = _ at h
  rw [h]
  have hb := (iteratedFDeriv ℝ n sin (L p)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  exact hb.trans (by nlinarith [(trig_jet_bound n).1 (L p), pow_nonneg (norm_nonneg L) n])

private theorem spacetime_sine_bound (T : ℝ) (n : ℕ) :
    ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry (fun t x : ℝ => sin (t+x))) p‖ ≤ M := by
  let L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
  refine ⟨‖L‖^n, fun p _ => ?_⟩
  simpa only [L, add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Function.uncurry_def] using sine_linear_frechet_bound L n p


private theorem cusp_bound : ∃ M, ∀ x : ℝ, abs (abs (sin x)) ≤ M :=
  ⟨1, fun x => by simpa only [abs_abs] using abs_sin_le_one x⟩


private theorem sine_space_deriv_bound (s x : ℝ) :
    |deriv (fun y => sin (s+y)) x| ≤ 1 := by
  have h : HasDerivAt (fun y : ℝ => sin (s+y)) (cos (s+x)) x := by
    simpa [Function.comp_def] using!
      (hasDerivAt_sin (s+x)).comp x ((hasDerivAt_id x).const_add s)
  rw [h.deriv]
  exact abs_cos_le_one _

-- Nonzero spatial forcing grows the bound with the exact viscosity factor.
example {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    |forcedBurgersSolution 3 (fun s y => sin (s+y)) (fun y => |sin y|) a t x| ≤ 1+6*t := by
  have h := abs_forcedBurgersSolution_le (ν := 3) (u₀ := fun y => |sin y|) (M := 1) (A := 1)
    (by norm_num) hT (by fun_prop) (by norm_num) (fun y => by
      simpa only [abs_abs] using abs_sin_le_one y)
    (by fun_prop) (spacetime_sine_bound T) (by norm_num)
    (fun s _ y => sine_space_deriv_bound s y) ht a x
  simpa only [mul_one, show (2 : ℝ)*3=6 by norm_num] using h

-- No bounded-primitive condition is present: a constant nonzero velocity is admitted.
example {ν T t : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    |forcedBurgersSolution ν (fun s y => sin (s+y)) (fun _ => 1) a t x| ≤ 1+2*ν*t := by
  simpa only [mul_one] using abs_forcedBurgersSolution_le (u₀ := fun _ => 1)
    (M := 1) (A := 1) hν hT continuous_const (by norm_num) (fun _ => by norm_num)
    (by fun_prop) (spacetime_sine_bound T) (by norm_num)
    (fun s _ y => sine_space_deriv_bound s y) ht a x

-- Spatially constant, time-varying potentials have no Burgers forcing.
example {ν T t : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    |forcedBurgersSolution ν (fun s _ => sin s) (fun y => |sin y|) a t x| ≤ 1 := by
  have hb (n : ℕ) : ∃ C, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry (fun s _ : ℝ => sin s)) p‖ ≤ C := by
    let L := ContinuousLinearMap.fst ℝ ℝ ℝ
    refine ⟨‖L‖^n,fun p _ => ?_⟩
    exact sine_linear_frechet_bound L n p
  simpa only [mul_zero,zero_mul,add_zero] using
    abs_forcedBurgersSolution_le (q := fun s _ => sin s) (M := 1) (A := 0)
      hν hT (by fun_prop) (by norm_num) (fun y => by
        simpa only [abs_abs] using abs_sin_le_one y) (by fun_prop) hb le_rfl
      (fun _ _ _ => by simp) ht a x

-- Zero potential recovers the unforced bound for the actual existing construction.
example {ν T t : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    |burgersSolution ν (fun y => |sin y|) a t x| ≤ 1 := by
  have hb (n : ℕ) : ∃ C, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry (fun _ _ : ℝ => (0 : ℝ))) p‖ ≤ C :=
    ⟨0,fun p _ => by simp [Function.uncurry_def]⟩
  simpa only [forcedBurgersSolution_zero_potential,mul_zero,zero_mul,add_zero] using
    abs_forcedBurgersSolution_le (q := fun _ _ => 0) (M := 1) (A := 0)
      hν hT (by fun_prop) (by norm_num) (fun y => by
        simpa only [abs_abs] using abs_sin_le_one y) (by fun_prop) hb le_rfl
      (fun _ _ _ => by simp) ht a x

-- Zero horizon is covered without a positive-time derivative hypothesis.
example {ν : ℝ} (hν : 0 < ν) (a x : ℝ) :
    |forcedBurgersSolution ν (fun s y => sin (s+y)) (fun y => |sin y|) a 0 x| ≤ 1 := by
  simpa only [mul_zero,add_zero] using abs_forcedBurgersSolution_le
    (M := 1) (A := 1) hν le_rfl (by fun_prop) (by norm_num)
    (fun y => by simpa only [abs_abs] using abs_sin_le_one y)
    (by fun_prop) (spacetime_sine_bound 0) (by norm_num)
    (fun s _ y => sine_space_deriv_bound s y) (t := 0) ⟨le_rfl,le_rfl⟩ a x

-- Terminal time is included although the PDE only holds on the open strip.
example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (a x : ℝ) :
    |forcedBurgersSolution ν (fun s y => sin (s+y)) (fun _ => 0) a T x| ≤ 2*ν*T := by
  simpa only [zero_add,mul_one] using abs_forcedBurgersSolution_le (u₀ := fun _ => 0)
    (M := 0) (A := 1) hν hT continuous_const le_rfl (fun _ => by simp)
    (by fun_prop) (spacetime_sine_bound T) (by norm_num)
    (fun s _ y => sine_space_deriv_bound s y) (t := T) ⟨hT,le_rfl⟩ a x

example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (a : ℝ) :
    ∃ C, ∀ t ∈ Icc 0 T, ∀ x,
      |forcedBurgersSolution ν (fun s y => sin (s+y)) (fun y => |sin y|) a t x| ≤ C :=
  forcedBurgersSolution_boundedOnStrip hν hT (by fun_prop) cusp_bound
    (by fun_prop) (spacetime_sine_bound T) a
