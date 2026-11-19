/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ODEBridge
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for the SIR ↔ integral-curve bridge

The disease-free constant solution (field vanishes, forward adapter), a field component at a
concrete point, local existence at a concrete epidemiological initial state, an explicit decaying
solution for `β = 0`, and a curve showing that an integral curve on `[0, ∞)` alone need not be a
solution (the one-sided gap at `0`).
-/

@[expose] public section

open Real Set
open MathlibExt.Biology.Epidemiology.SIR

namespace MathlibExtTest.Biology.Dynamics.ODEBridge

/-- The disease-free state `(c, 0, d)` is a constant solution. -/
theorem diseaseFree_isSolution (β γ N c d : ℝ) :
    IsSolution β γ N (fun _ => c) (fun _ => 0) (fun _ => d) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t c
  hasDerivAt_infected t _ := by simpa using hasDerivAt_const t (0 : ℝ)
  hasDerivAt_removed t _ := by simpa using hasDerivAt_const t d

/-- The SIR field vanishes at a disease-free state. -/
example (β γ N c d t : ℝ) : sirField β γ N t ![c, 0, d] = 0 := by
  ext i
  fin_cases i <;> simp [sirField]

/-- The packed disease-free solution is an integral curve on `[0, ∞)`. -/
example (β γ N c d : ℝ) :
    IsIntegralCurveOn (sirCurve (fun _ => c) (fun _ => 0) (fun _ => d)) (sirField β γ N)
      (Ici 0) :=
  (diseaseFree_isSolution β γ N c d).isIntegralCurveOn_Ici

/-- Infective component of the field at `(S, I, R) = (0.99, 0.01, 0)` with `β = 2`, `γ = 1`,
`N = 1`: `2 · 0.99 · 0.01 - 0.01 = 0.0098`. -/
example : sirField 2 1 1 0 ![99 / 100, 1 / 100, 0] 1 = 49 / 5000 := by
  norm_num [sirField]

/-- Susceptible and removed components at the same point. -/
example : sirField 2 1 1 0 ![99 / 100, 1 / 100, 0] 0 = -(99 / 5000) ∧
    sirField 2 1 1 0 ![99 / 100, 1 / 100, 0] 2 = 1 / 100 := by
  norm_num [sirField]

/-- Local existence from the initial state `(0.99, 0.01, 0)` with `β = 2`, `γ = 1`, `N = 1`. -/
example : ∃ ε > (0 : ℝ), ∃ α : ℝ → Fin 3 → ℝ, α 0 1 = 1 / 100 ∧
    IsIntegralCurveOn α (sirField 2 1 1) (Icc (-ε) ε) := by
  obtain ⟨ε, hε, α, h0, h⟩ := exists_isIntegralCurveOn_Icc 2 1 1 ![99 / 100, 1 / 100, 0]
  exact ⟨ε, hε, α, by simp [h0], h⟩

/-- Local existence in compartment form, with the initial values recovered. -/
example : ∃ ε > (0 : ℝ), ∃ S I R : ℝ → ℝ, S 0 = 99 / 100 ∧ I 0 = 1 / 100 ∧ R 0 = 0 := by
  obtain ⟨ε, hε, S, I, R, hS, hI, hR, -⟩ := exists_sir_hasDerivWithinAt_Icc 2 1 1 (99 / 100)
    (1 / 100) 0
  exact ⟨ε, hε, S, I, R, hS, hI, hR⟩

/-- Local curves from the same initial point agree near `0`. -/
example (x₀ : Fin 3 → ℝ) : ∃ ε > (0 : ℝ), ∃ α : ℝ → Fin 3 → ℝ, α 0 = x₀ ∧
    ∀ α' : ℝ → Fin 3 → ℝ, α' 0 = x₀ → IsIntegralCurveOn α' (sirField 2 1 1) (Icc (-ε) ε) →
      EqOn α α' (Icc (-ε) ε) := by
  obtain ⟨ε, hε, α, h0, h⟩ := exists_isIntegralCurveOn_Icc 2 1 1 x₀
  refine ⟨ε, hε, α, h0, fun α' h0' h' => ?_⟩
  simpa using eqOn_of_isIntegralCurveOn_Icc_zero hε hε h h' (h0.trans h0'.symm)

/-- For `β = 0` there is no transmission: `S` is constant and `I` decays exponentially into `R`. -/
example (γ N c I₀ R₀ : ℝ) :
    IsSolution 0 γ N (fun _ => c) (fun t => I₀ * exp (-γ * t))
      (fun t => R₀ + I₀ * (1 - exp (-γ * t))) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t c
  hasDerivAt_infected t _ := by
    have := (((hasDerivAt_id' t).const_mul (-γ)).exp).const_mul I₀
    convert this using 1
    simp
    ring
  hasDerivAt_removed t _ := by
    have := ((((hasDerivAt_id' t).const_mul (-γ)).exp).const_sub 1).const_mul I₀ |>.const_add R₀
    convert this using 1
    simp
    ring

/-- **The one-sided gap at `0`.** With `β = γ = 0` the field vanishes, and the curve
`(0, 0, |t| - t)` is an integral curve on `[0, ∞)` (it is identically `0` there) but is not a
solution: its `R`-component has a corner at `0`. -/
example (N : ℝ) :
    IsIntegralCurveOn (fun t => ![0, 0, |t| - t]) (sirField 0 0 N) (Ici 0) ∧
      ¬ IsSolution 0 0 N (fun _ => 0) (fun _ => 0) (fun t => |t| - t) := by
  refine ⟨fun t ht => ?_, fun h => ?_⟩
  · have hfield : sirField 0 0 N t ![0, 0, |t| - t] = 0 := by
      ext i
      fin_cases i <;> simp [sirField]
    rw [hfield]
    refine (hasDerivWithinAt_const t (Ici 0) (0 : Fin 3 → ℝ)).congr (fun s hs => ?_) ?_
    · simp [abs_of_nonneg (mem_Ici.1 hs)]
    · simp [abs_of_nonneg (mem_Ici.1 ht)]
  · have hR := (h.hasDerivAt_removed 0 le_rfl).differentiableAt.add differentiableAt_id
    exact not_differentiableAt_abs_zero (by simpa using hR)

end MathlibExtTest.Biology.Dynamics.ODEBridge
