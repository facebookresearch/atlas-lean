/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.ForcedBurgersSinePotential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Set Real
open ColeHopf

-- The actual initial-value construction, not an assumed profile, has this value.
example (a x t : ℝ) (ht : 0 ≤ t) :
    forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a t x = -6*t*cos x := by
  rw [forcedBurgersSolution_sinePotential (by norm_num : (0 : ℝ) < 3) ht]
  ring

-- High-order joint Frechet bounds are derived, including at negative viscosity.
example (T : ℝ) : ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
    ‖iteratedFDeriv ℝ 7 (Function.uncurry (sinePotential (-3))) p‖ ≤ M :=
  sinePotential_bounded_jets (-3) T 7

-- Identify the actual potential-heat evolution at nonzero time and space.
example : MathlibExt.Analysis.PDE.HeatKernel.potentialHeatSolution 3 (sinePotential 3)
    (fun _ => 1) 2 (π/2) = exp 2 := by
  simpa using potentialHeatSolution_sinePotential (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) ≤ 2) (π/2)

example (a x : ℝ) :
    forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a 0 x = 0 := by
  simpa only [mul_zero,zero_mul] using
    forcedBurgersSolution_sinePotential (by norm_num : (0 : ℝ) < 3) le_rfl a x

-- Nonunit viscosity and a point where both sine and cosine are nonzero.
example (a : ℝ) :
    forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a 1 (π/4) = -3*sqrt 2 := by
  rw [forcedBurgersSolution_sinePotential (by norm_num) (by norm_num),cos_pi_div_four]
  ring

-- The example also meets every hypothesis of the bounded classical uniqueness class.
example (T : ℝ) (hT : 0 ≤ T) (a : ℝ) :
    IsBoundedForcedBurgersSolutionOn 3 (sinePotential 3) (fun _ => 0) T
      (forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a) :=
  forcedBurgersSolution_isBoundedForcedBurgersSolutionOn (by norm_num) hT continuous_const
    ⟨0,fun _ => by norm_num⟩ (sinePotential_contDiff 3) (sinePotential_bounded_jets 3 T) a

-- Any bounded classical competitor has this explicit value, including terminal time.
example {v : ℝ → ℝ → ℝ} (T : ℝ) (hT : 0 ≤ T)
    (hv : IsBoundedForcedBurgersSolutionOn 3 (sinePotential 3) (fun _ => 0) T v) (x : ℝ) :
    v T x = -6*T*cos x := by
  rw [hv.eq_forcedBurgersSolution_of_contDiff (by norm_num) hT (sinePotential_contDiff 3)
    (sinePotential_bounded_jets 3 T) 0 T ⟨hT,le_rfl⟩ x,
    forcedBurgersSolution_sinePotential (by norm_num) hT]
  ring

private theorem sine_potential_hasDerivAt (ν t x : ℝ) :
    HasDerivAt (sinePotential ν t)
      ((1+ν*t)*cos x+2*ν*t^2*cos x*sin x) x := by
  have h := ((hasDerivAt_sin x).add ((hasDerivAt_sin x).const_mul (ν*t))).sub
    (((hasDerivAt_cos x).pow 2).const_mul (ν*t^2))
  convert h using 1
  · funext y
    simp only [sinePotential,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
  · ring

-- Check the actual PDE residual at a point exercising the nonlinear forcing term.
-- For nu=3,t=1,x=pi/4, -2nu*q_x is exactly -18-12sqrt(2).
example (a : ℝ) :
    deriv (fun s => forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a s (π/4)) 1 +
      forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a 1 (π/4) *
        deriv (forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a 1) (π/4) -
      3 * iteratedDeriv 2 (forcedBurgersSolution 3 (sinePotential 3) (fun _ => 0) a 1) (π/4) =
        -18-12*sqrt 2 := by
  rw [forcedBurgersSolution_forced_burgers (T := 2) (by norm_num) continuous_const
    ⟨0,fun _ => by norm_num⟩ (sinePotential_contDiff 3) (sinePotential_bounded_jets 3 2)
    (by constructor <;> norm_num) a (π/4),
    (sine_potential_hasDerivAt 3 1 (π/4)).deriv,cos_pi_div_four,sin_pi_div_four]
  nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
