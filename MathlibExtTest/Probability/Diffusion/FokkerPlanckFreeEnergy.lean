/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.FokkerPlanckFreeEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Tests for free-energy decay of the gradient-drift Fokker–Planck equation

Non-vacuity witness (non-stationary): with `Ψ = 0`, `D = 1` on `[0, 1]`, the Neumann heat
solution `p(t, x) = 1 + e^{-π² t} cos (π x) / 2` solves the no-flux equation for all `t`, is
`C²`, and is positive for `t > 0`. The free-energy theorems then apply on `I = (0, ∞)`.
-/

@[expose] public section

open Set Real MathlibExt.Probability.FokkerPlanck

namespace MathlibExtTest.Probability.Diffusion.FokkerPlanckFreeEnergy

/-- A decaying Neumann heat mode on `[0, 1]`. -/
noncomputable def heat (t x : ℝ) : ℝ := 1 + exp (-(π ^ 2 * t)) * cos (π * x) / 2

private lemma hasDerivAt_heat_x (t x : ℝ) :
    HasDerivAt (fun y => heat t y) (-(exp (-(π ^ 2 * t)) * sin (π * x) * π / 2)) x := by
  have hc : HasDerivAt (fun y => cos (π * y)) (-sin (π * x) * π) x := by
    simpa using ((hasDerivAt_id x).const_mul π).cos
  have h := ((hc.const_mul (exp (-(π ^ 2 * t)))).div_const 2).const_add 1
  unfold heat
  convert h using 1
  ring

private lemma hasDerivAt_heat_t (t x : ℝ) :
    HasDerivAt (fun s => heat s x) (exp (-(π ^ 2 * t)) * (-(π ^ 2)) * cos (π * x) / 2) t := by
  have he : HasDerivAt (fun s => exp (-(π ^ 2 * s))) (exp (-(π ^ 2 * t)) * (-(π ^ 2))) t := by
    simpa using (((hasDerivAt_id t).const_mul (π ^ 2)).neg).exp
  have h := ((he.mul_const (cos (π * x))).div_const 2).const_add 1
  unfold heat
  exact h

private lemma negFlux_heat (t : ℝ) :
    negFlux (fun _ => 0) 1 heat t = fun x => -(exp (-(π ^ 2 * t)) * sin (π * x) * π / 2) := by
  funext x
  simp [negFlux, (hasDerivAt_heat_x t x).deriv]

private lemma hasDerivAt_negFlux_heat (t x : ℝ) :
    HasDerivAt (negFlux (fun _ => 0) 1 heat t)
      (exp (-(π ^ 2 * t)) * (-(π ^ 2)) * cos (π * x) / 2) x := by
  have hs : HasDerivAt (fun y => sin (π * y)) (cos (π * x) * π) x := by
    simpa using ((hasDerivAt_id x).const_mul π).sin
  have h := (((hs.const_mul (exp (-(π ^ 2 * t)))).mul_const π).div_const 2).neg
  rw [negFlux_heat]
  convert h using 1
  ring

theorem heat_isNoFluxSolutionOn : IsNoFluxSolutionOn (fun _ => 0) 1 0 1 univ heat where
  pde t _ x _ := by rw [(hasDerivAt_heat_t t x).deriv, (hasDerivAt_negFlux_heat t x).deriv]
  flux_left t _ := by simp [negFlux_heat]
  flux_right t _ := by simp [negFlux_heat, sin_pi]

theorem heat_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heat t x := by
  have hpt : 0 < π ^ 2 * t := mul_pos (pow_pos pi_pos 2) ht
  have h1 : exp (-(π ^ 2 * t)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h2 : 0 < exp (-(π ^ 2 * t)) := exp_pos _
  have h3 := neg_one_le_cos (π * x)
  unfold heat
  nlinarith

theorem heat_contDiff : ContDiff ℝ 2 (Function.uncurry heat) := by
  unfold heat Function.uncurry
  fun_prop

-- The hypotheses of the free-energy theorems hold on `I = (0, ∞)`, so the free energy of the
-- heat mode is nonincreasing for `t > 0`.
example : AntitoneOn (freeEnergy (fun _ => 0) 1 0 1 heat) (Ioi 0) :=
  antitoneOn_freeEnergy zero_le_one isOpen_Ioi (convex_Ioi 0) contDiff_const heat_contDiff
    (fun _ ht x => heat_pos ht x)
    ⟨fun t _ x hx => heat_isNoFluxSolutionOn.pde t trivial x hx,
      fun t _ => heat_isNoFluxSolutionOn.flux_left t trivial,
      fun t _ => heat_isNoFluxSolutionOn.flux_right t trivial⟩

-- Mass conservation for the heat mode at any time.
example (t : ℝ) : HasDerivAt (fun s => ∫ x in (0 : ℝ)..1, heat s x) 0 t :=
  hasDerivAt_mass zero_le_one contDiff_const heat_contDiff heat_isNoFluxSolutionOn (mem_univ t)

end MathlibExtTest.Probability.Diffusion.FokkerPlanckFreeEnergy
