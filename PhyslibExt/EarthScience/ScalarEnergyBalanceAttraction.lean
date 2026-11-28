/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Mul
import MathlibExt.Analysis.ODE.MaximalSolution
import MathlibExt.Analysis.ODE.ScalarStability
import MathlibExt.Analysis.ODE.TubeBootstrap

/-!
# Local attraction in a scalar energy-balance model

Nearby initial temperatures converge exponentially to a negative-slope equilibrium.

## i. Overview

At a fixed parameter value, let `F` be the net energy flux and `C > 0` the heat capacity.
Only the flux near the equilibrium needs to be continuously differentiable.

## ii. Key results

- `EarthScience.local_attraction_in_a_scalar_energy_balance_model`: forward existence,
  uniqueness and uniform exponential attraction for `C * T' = F(T)`.

## iii. Table of contents

- A. Local attraction

## iv. References

This is a scalar deduction. Extend the locally Lipschitz rate `F / C` by
`LipschitzOnWith.extend_real` and solve the extended equation by
`MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz`.
The conditional estimate `MathlibExt.Analysis.ODE.ScalarStability.scalar_sign_decay_of_hasDerivAt`
then keeps the resulting trajectory strictly inside the region of agreement. For uniqueness,
`MathlibExt.Analysis.ODE.TubeBootstrap.tube_bootstrap` gives zero distance from this trajectory
on each finite forward interval, without assuming the competing solution stays in that region.
-/

@[expose] public section

namespace EarthScience

open Filter Metric Set
open scoped Topology

/-! ## A. Local attraction -/

/-- Fix a heat capacity `C > 0`. Suppose the net flux `F` is continuously differentiable near
`Tstar`, with `F(Tstar) = 0` and `F′(Tstar) < 0`. There are constants `δ, K, α > 0` such that
for every `T₀` with `|T₀ - Tstar| < δ`, the equation `C * T' = F(T)` has a solution on `[0, ∞)`
with `T(0) = T₀` and `|T(t) - Tstar| ≤ K * exp(-α * t) * |T₀ - Tstar|` for every `t ≥ 0`.
The derivative at zero is taken from the right. Any other forward solution with the same initial
temperature agrees with `T` on `[0, ∞)`. -/
lemma local_attraction_in_a_scalar_energy_balance_model {F : ℝ → ℝ} {C Tstar : ℝ}
    (hC : 0 < C) (hF : ContDiffAt ℝ 1 F Tstar) (heq : F Tstar = 0)
    (hneg : deriv F Tstar < 0) :
    ∃ δ K α : ℝ, 0 < δ ∧ 0 < K ∧ 0 < α ∧ ∀ T₀ : ℝ, |T₀ - Tstar| < δ →
      ∃ T : ℝ → ℝ, T 0 = T₀ ∧ IsIntegralCurveOn T (fun _ u => F u / C) (Ici 0) ∧
        (∀ t ≥ 0, |T t - Tstar| ≤ K * Real.exp (-(α * t)) * |T₀ - Tstar|) ∧
        ∀ S : ℝ → ℝ, S 0 = T₀ → IsIntegralCurveOn S (fun _ u => F u / C) (Ici 0) →
          EqOn S T (Ici 0) := by
  obtain ⟨L, N, hN, hlip⟩ := (hF.div_const C).exists_lipschitzOnWith
  obtain ⟨g, hg, hfg⟩ := hlip.extend_real
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hN
  have hagree : g =ᶠ[𝓝 Tstar] (fun u => F u / C) := hfg.symm.eventuallyEq_of_mem hN
  have hg₀ : g Tstar = 0 := by rw [hagree.eq_of_nhds, heq, zero_div]
  have hgd : HasDerivAt g (deriv F Tstar / C) Tstar :=
    (hF.differentiableAt_one.hasDerivAt.div_const C).congr_of_eventuallyEq hagree
  obtain ⟨d, K, α, hd, hK, hα, hdecay⟩ :=
    MathlibExt.Analysis.ODE.ScalarStability.scalar_sign_decay_of_hasDerivAt
      hg₀ hgd (div_neg_of_neg_of_pos hneg hC)
  -- Reserve half the radius for a tube around the extended solution.
  refine ⟨min d (r / 2 / K), K, α, lt_min hd (by positivity), hK, hα, ?_⟩
  intro T₀ h₀
  obtain ⟨T, ⟨hT₀, hT⟩, -⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      (fun _ => g) 0 T₀ L (hg.continuous.comp continuous_snd) (fun _ => hg)
  have hbound := hdecay T (fun t _ => hT t) (by rw [hT₀]; exact h₀.trans_le (min_le_left ..))
  rw [hT₀] at hbound
  have hnear (t : ℝ) (ht : 0 ≤ t) : dist (T t) Tstar < r / 2 := by
    rw [Real.dist_eq]
    calc |T t - Tstar| ≤ K * Real.exp (-(α * t)) * |T₀ - Tstar| := hbound t ht
      _ ≤ K * 1 * |T₀ - Tstar| := by
        gcongr
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hα.le ht))
      _ < r / 2 := by
        simpa [mul_comm] using (lt_div_iff₀ hK).mp (h₀.trans_le (min_le_right ..))
  have htube (t : ℝ) (ht : 0 ≤ t) : EqOn (fun u => F u / C) g (closedBall (T t) (r / 2)) := by
    intro u hu
    apply hfg (hball ?_)
    calc dist u Tstar ≤ dist u (T t) + dist (T t) Tstar := dist_triangle ..
      _ < r := by linarith [mem_closedBall.mp hu, hnear t ht]
  refine ⟨T, hT₀, fun t ht => ?_, hbound, ?_⟩
  · simpa only [← htube t ht (mem_closedBall_self (half_pos hr).le)] using
      (hT t).hasDerivWithinAt (s := Ici 0)
  intro S hS₀ hS b hb
  have hdist := MathlibExt.Analysis.ODE.TubeBootstrap.tube_bootstrap
    (v := fun _ => g) (f := T) (g := S) (g' := fun t => F (S t) / C)
    (δ := 0) (ε := 0) (K := L) hb le_rfl (half_pos hr)
    (by simpa only [gronwallBound_ε0_δ0] using half_pos hr)
    (fun _ _ => hg.lipschitzOnWith) (fun t _ => (hT t).continuousAt.continuousWithinAt)
    (fun t _ => (hT t).hasDerivWithinAt) (hS.continuousOn.mono Icc_subset_Ici_self)
    (fun t ht hu => ⟨(hS t ht.1).mono (Ici_subset_Ici.mpr ht.1),
      dist_le_zero.mpr (htube t ht.1 hu)⟩) (by simp [hT₀, hS₀]) b ⟨hb, le_rfl⟩
  exact (dist_le_zero.mp (by simpa only [gronwallBound_ε0_δ0] using hdist.2)).symm

end EarthScience
