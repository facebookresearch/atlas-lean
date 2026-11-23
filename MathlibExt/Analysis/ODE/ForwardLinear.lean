/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.Analysis.ODE.Duhamel

/-!
# Forward linear evolution agreement

For a bounded real linear operator `A` and forcing `b` continuous
only on `[0, ∞)`, the Duhamel construction restricts to the unique
continuous forward trajectory with right derivatives
`x'(t) = A x(t) + b(t)`. Negative-time values of a forward-only
comparison curve are unconstrained and irrelevant.
-/

@[expose] public section

open Set Filter Topology

namespace MathlibExt.Analysis.ODE.ForwardLinear

/-- **Forward Duhamel agreement.** The Duhamel trajectory for the
extended forcing is the unique forward solution: every forward
curve with the same initial value and right derivatives agrees
with it on `[0, ∞)`. -/
theorem forward_duhamel_eqOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {b : ℝ → E} (hb : ContinuousOn b (Ici 0))
    (x₀ : E) {y : ℝ → E} (hy0 : y 0 = x₀) (hy_cont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t → HasDerivWithinAt y (A (y t) + b t) (Ici t) t) :
    EqOn y (fun t => (NormedSpace.exp (t • A)) x₀ +
      ∫ s in (0:ℝ)..t, (NormedSpace.exp ((t - s) • A)) (b s)) (Ici 0) := by
  have hb' : Continuous (fun t => b (max t 0)) := by
    exact hb.comp_continuous (continuous_id.max continuous_const)
      (fun t => mem_Ici.mpr (le_max_right t 0))
  obtain ⟨x, hx0, hxform, hxderiv, -⟩ :=
    MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants A
      (fun t => b (max t 0)) 0 x₀ hb'
  have hx_eq : ∀ t, 0 ≤ t → x t = (NormedSpace.exp (t • A)) x₀ +
      ∫ s in (0:ℝ)..t, (NormedSpace.exp ((t - s) • A)) (b s) := by
    intro t ht
    rw [hxform t]
    congr 1
    · simp
    · apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : (0:ℝ) ≤ s := by
        have h1 : min (0:ℝ) t ≤ s := hs.1
        rwa [min_eq_left ht] at h1
      show (NormedSpace.exp ((t - s) • A)) (b (max s 0)) =
        (NormedSpace.exp ((t - s) • A)) (b s)
      rw [max_eq_left hs0]
  have hx_cont : Continuous x := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hxderiv t).continuousAt
  intro T hT
  have hEq := ODE_solution_unique_of_mem_Icc_right (a := (0:ℝ)) (b := T)
    (v := fun t z => A z + b t) (s := fun _ => univ) (K := ‖A‖₊)
    (fun t _ => by simpa only [add_zero] using (A.lipschitzWith.add (LipschitzWith.const (b t))).lipschitzOnWith)
    (hy_cont.mono (fun z hz => mem_Ici.mpr hz.1))
    (fun t ht => hy t (mem_Ico.mp ht).1)
    (fun _ _ => mem_univ _)
    (hx_cont.continuousOn)
    (fun t ht => by
      have ht0 : (0:ℝ) ≤ t := (mem_Ico.mp ht).1
      have h := (hxderiv t).hasDerivWithinAt (s := Ici t)
      rwa [max_eq_left ht0] at h)
    (fun _ _ => mem_univ _)
    (by rw [hy0, hx0])
  have hTmem : T ∈ Icc (0:ℝ) T := right_mem_Icc.mpr hT
  have := hEq hTmem
  rw [hx_eq T hT] at this
  exact this

end MathlibExt.Analysis.ODE.ForwardLinear
