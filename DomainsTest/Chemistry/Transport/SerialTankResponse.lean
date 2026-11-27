/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Transport.SerialTankResponse
import Mathlib.Tactic.NormNum

/-!
# Fixtures for the serial compartment response

One compartment has the exponential density. In two compartments at unit rate and unit initial
amount, the profiles are `exp (-t)` and `t * exp (-t)`, and the second profile gives the
normalized outflow on nonnegative time.
-/

open Chemistry.Transport MeasureTheory

/-- One compartment has the expected initial-value solution and a normalized exponential
outflow, with the same symbolic time parameter in both formulas. -/
example (τ : ℝ) (hτ : 0 < τ) (u : Fin 1 → ℝ → ℝ) (hu : u 0 0 = 1)
    (hdu : ∀ t, 0 ≤ t → HasDerivAt (u 0) (-τ⁻¹ * u 0 t) t) :
    (∀ t, 0 ≤ t → u 0 t = Real.exp (-(τ⁻¹ * t))) ∧
      (∫ t : ℝ, if 0 ≤ t then τ⁻¹ * Real.exp (-(τ⁻¹ * t)) else 0) = 1 := by
  obtain ⟨_, huniq, _, _, _, hint⟩ := serialTank_bolusResponse 0 τ 1 hτ one_pos
  refine ⟨?_, ?_⟩
  · intro t ht
    have h := huniq u
      ⟨hu, fun j ↦ j.elim0, by simpa [one_div] using hdu, fun j ↦ j.elim0⟩ 0 t ht
    simpa [one_div] using h
  · simpa [one_div] using hint

/-- The two-compartment fixture checks the predecessor and the last index, and the
normalization of the outflow obtained from an arbitrary solution. -/
example (u : Fin 2 → ℝ → ℝ) (hu₀ : u 0 0 = 1) (hu₁ : u 1 0 = 0)
    (hdu₀ : ∀ t, 0 ≤ t → HasDerivAt (u 0) (-u 0 t) t)
    (hdu₁ : ∀ t, 0 ≤ t → HasDerivAt (u 1) (u 0 t - u 1 t) t) :
    (∀ t, 0 ≤ t → u 0 t = Real.exp (-t) ∧ u 1 t = t * Real.exp (-t)) ∧
      (∀ t : ℝ, (if 0 ≤ t then u 1 t else 0) =
        if 0 ≤ t then t * Real.exp (-t) else 0) ∧
      (∫ t : ℝ, if 0 ≤ t then u 1 t else 0) = 1 := by
  obtain ⟨_, huniq, _, _, _, hint⟩ :=
    serialTank_bolusResponse 1 2 1 (by norm_num) one_pos
  have hu (j : Fin 2) (t : ℝ) (ht : 0 ≤ t) := huniq u (by
    refine ⟨hu₀, ?_, ?_, ?_⟩
    · intro i
      rw [Subsingleton.elim i 0]
      exact hu₁
    · intro s hs
      norm_num
      simpa only [neg_one_mul] using hdu₀ s hs
    · intro i s hs
      rw [Subsingleton.elim i 0]
      norm_num
      exact hdu₁ s hs) j t ht
  have hprofiles (t : ℝ) (ht : 0 ≤ t) :
      u 0 t = Real.exp (-t) ∧ u 1 t = t * Real.exp (-t) := by
    constructor
    · simpa using hu 0 t ht
    · simpa using hu 1 t ht
  have hout (t : ℝ) :
      (if 0 ≤ t then u 1 t else 0) = if 0 ≤ t then t * Real.exp (-t) else 0 := by
    by_cases ht : 0 ≤ t
    · simp [ht, (hprofiles t ht).2]
    · simp [ht]
  refine ⟨hprofiles, hout, ?_⟩
  simp_rw [hout]
  simpa using hint

/-- The explicit second profile has an ordinary derivative at the initial time. -/
example : HasDerivAt (fun t : ℝ ↦ t * Real.exp (-t)) 1 0 := by
  have h := (serialTank_bolusResponse 1 2 1 (by norm_num) one_pos).1.2.2.2 0 0 le_rfl
  simpa using h
