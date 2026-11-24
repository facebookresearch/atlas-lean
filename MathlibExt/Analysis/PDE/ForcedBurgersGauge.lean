/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.PotentialHeatGauge
public import MathlibExt.Analysis.PDE.ForcedBurgersInitialValue

/-!
# Time-only potential compatibility for forced Burgers

The actual forced Burgers field is unchanged when a continuous time-only term is
added to the potential. The actual potential-heat profiles differ by a strictly
positive scalar depending only on time; spatial differentiation and division
cancel it. The identity includes both endpoints of a finite strip and only needs
finite spatial C2 potential regularity. In particular, a purely time-dependent
potential gives the existing unforced Burgers construction.

The integrating-factor background is Gesztesy and Holden, *The Cole–Hopf and
Miura transformations revisited*, Theorem 3.3 and Remark 3.4,
https://arxiv.org/abs/solv-int/9812025.
-/

@[expose] public section

open Set Real MeasureTheory
open scoped ContDiff Interval
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- Adding a continuous time-only potential leaves the actual forced Burgers
velocity unchanged on the closed strip. No time derivative of the potential or
initial velocity derivative is required. -/
theorem forcedBurgersSolution_add_time_potential
    {q : ℝ → ℝ → ℝ} {u₀ r : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hr : ContinuousOn r (Icc 0 T)) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    forcedBurgersSolution ν (fun s y => q s y+r s) u₀ a t x =
      forcedBurgersSolution ν q u₀ a t x := by
  have he : forcedBurgersProfile ν (fun s y => q s y+r s) u₀ a t =
      fun y => exp (∫ s in 0..t, r s) * forcedBurgersProfile ν q u₀ a t y :=
    funext (fun y => potentialHeatSolution_add_time_potential hν hT hqs hqc hqb
      (initialHeatProfile_contDiff hu ν a).continuous (initialHeatProfile_hasExpGrowth hub hν a)
      hr ht y)
  simp only [forcedBurgersSolution,classicalTransform,he,deriv_const_mul_field,
    mul_div_mul_left _ _ (ne_of_gt (exp_pos _))]

/-- Purely time-dependent potentials give the actual unforced Burgers solution,
including the initial and terminal times of every finite strip of continuity. -/
theorem forcedBurgersSolution_time_potential
    {u₀ r : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hr : ContinuousOn r (Icc 0 T)) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    forcedBurgersSolution ν (fun s _ => r s) u₀ a t x = burgersSolution ν u₀ a t x := by
  simpa only [zero_add,forcedBurgersSolution_zero_potential] using
    forcedBurgersSolution_add_time_potential (q := fun _ _ => 0) hν hT hu hub
      (fun _ _ => contDiff_const)
      (fun k _ => by simp only [iteratedDeriv_fun_const_zero]; fun_prop)
      (fun k _ => ⟨0,fun _ _ _ => by simp⟩) hr ht a x

end ColeHopf
