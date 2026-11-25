/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.ForcedBurgersInitialValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open Set Filter Real
open scoped ContDiff Topology
open ColeHopf

-- Continuous initial velocities with spatial cusps are recovered exactly.
example {ν : ℝ} (hν : ν ≠ 0) (q : ℝ → ℝ → ℝ) (a x : ℝ) :
    forcedBurgersSolution ν q (fun y => |sin y|) a 0 x = |sin x| :=
  forcedBurgersSolution_initial (by fun_prop) hν q a x

example (ν : ℝ) (u₀ : ℝ → ℝ) (a t x : ℝ) :
    forcedBurgersSolution ν (fun _ _ => 0) u₀ a t x = burgersSolution ν u₀ a t x :=
  forcedBurgersSolution_zero_potential ν u₀ a t x

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

-- Positivity needs no positive lower bound on the exponential primitive.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    0 < forcedBurgersProfile ν (fun s y => sin (s+y)) (fun _ => 1) a t x :=
  forcedBurgersProfile_pos hν continuous_const ⟨1, fun _ => by norm_num⟩
    (by fun_prop) (spacetime_sine_bound T) ht a x

-- Joint closed-strip continuity includes both initial and terminal time for cusp data.
example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (a : ℝ) :
    ContinuousOn (Function.uncurry (forcedBurgersSolution ν
      (fun s y => sin (s+y)) (fun y => |sin y|) a)) (Icc 0 T ×ˢ univ) :=
  forcedBurgersSolution_continuousOn hν hT (by fun_prop) cusp_bound
    (by fun_prop) (spacetime_sine_bound T) a

example {ν T : ℝ} (hν : 0 < ν) (a : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (forcedBurgersSolution ν
      (fun s y => sin (s+y)) (fun y => |sin y|) a)) (Ioo 0 T ×ˢ univ) :=
  forcedBurgersSolution_contDiffOn hν (by fun_prop) cusp_bound
    (by fun_prop) (spacetime_sine_bound T) a

-- The joint trace allows space and time to approach the initial point together.
example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (a x : ℝ) :
    Tendsto (Function.uncurry (forcedBurgersSolution ν
      (fun s y => sin (s+y)) (fun y => |sin y|) a))
      (𝓝[Icc 0 T ×ˢ univ] (0,x)) (𝓝 (|sin x|)) :=
  forcedBurgersSolution_tendsto_initial hν hT (by fun_prop) cusp_bound
    (by fun_prop) (spacetime_sine_bound T) a x

-- Nonunit viscosity and a nonzero forcing point distinguish the sign and coefficient.
example {T : ℝ} (hT : 1 < T) (a : ℝ) :
    let u := forcedBurgersSolution 3 (fun s y => sin (s+y)) (fun y => |sin y|) a
    deriv (fun s => u s (-1)) 1 + u 1 (-1) * deriv (u 1) (-1) -
      3 * iteratedDeriv 2 (u 1) (-1) = -6 := by
  have hq : HasDerivAt (fun y : ℝ => sin (1+y)) 1 (-1) := by
    simpa [Function.comp_def] using!
      (hasDerivAt_sin (1+(-1 : ℝ))).comp (-1) ((hasDerivAt_id (-1 : ℝ)).const_add 1)
  have h := forcedBurgersSolution_forced_burgers (ν := 3) (q := fun s y => sin (s+y)) (u₀ := fun y => |sin y|)
    (by norm_num) (by fun_prop) cusp_bound (by fun_prop) (spacetime_sine_bound T)
    (t := 1) ⟨by norm_num,hT⟩ a (-1)
  simpa only [hq.deriv, mul_one, show (-2 : ℝ)*3 = -6 by norm_num] using h

-- The zero horizon still supports the initial trace; no positive-time equation is claimed.
example {ν : ℝ} (hν : 0 < ν) (a x : ℝ) :
    Tendsto (Function.uncurry (forcedBurgersSolution ν
      (fun s y => sin (s+y)) (fun y => |sin y|) a))
      (𝓝[Icc 0 0 ×ˢ univ] (0,x)) (𝓝 (|sin x|)) :=
  forcedBurgersSolution_tendsto_initial hν le_rfl (by fun_prop) cusp_bound
    (by fun_prop) (spacetime_sine_bound 0) a x

-- Positive-time smoothness has an empty domain when the horizon is zero.
example {ν : ℝ} (hν : 0 < ν) (a : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (forcedBurgersSolution ν
      (fun s y => sin (s+y)) (fun y => |sin y|) a)) (Ioo 0 0 ×ˢ univ) :=
  forcedBurgersSolution_contDiffOn hν (by fun_prop) cusp_bound
    (by fun_prop) (spacetime_sine_bound 0) a
