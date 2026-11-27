/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum

import PhyslibExt.Mechanics.VibroacousticEnergy

/-!
# Vibroacoustic port-energy checks

Focused checks for `PhyslibExt.Mechanics.VibroacousticEnergy`:
a one-coordinate decaying exponential solution
`x(τ) = e^{-τ}`, `v(τ) = -e^{-τ}`, `p(τ) = -e^{-τ}` of the
coupled system with unit mass, stiffness, and coupling,
structural damping `3`, acoustic storage `2`, and acoustic
damping `1`. Both quadratic damping terms are positive at
`t = 0`, and the quadratic form has the concrete nonzero
derivative `-4` there.

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix

/-- The identity at the decaying exponential solution, with
the concrete derivative value `-4` at `t = 0`. -/
example : HasDerivAt
    (fun τ => (1 / 2) * (((fun _ => -Real.exp (-τ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => -Real.exp (-τ)) : Fin 1 → ℝ))
      + ((fun _ => Real.exp (-τ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => Real.exp (-τ)) : Fin 1 → ℝ))
      + ((fun _ => -Real.exp (-τ)) : Fin 1 → ℝ)
        ⬝ᵥ (((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          *ᵥ ((fun _ => -Real.exp (-τ)) : Fin 1 → ℝ))))
    (-4) 0 := by
  have hexp : ∀ t : ℝ,
      HasDerivAt (fun τ : ℝ => Real.exp (-τ)) (-Real.exp (-t)) t :=
    fun t => by
      simpa using (hasDerivAt_neg' t).exp
  have h := Mechanics.Vibroacoustic.vibroacoustic_port_energy
    (n := Fin 1) (m := Fin 1) (M := 1) (K := 1) (C := (3 : ℝ) • 1) (A := (2 : ℝ) • 1)
    (H := 1) (G := 1)
    (x := fun τ _ => Real.exp (-τ))
    (v := fun τ _ => -Real.exp (-τ))
    (dv := fun τ _ => Real.exp (-τ))
    (p := fun τ _ => -Real.exp (-τ))
    (dp := fun τ _ => Real.exp (-τ))
    (by simp [Matrix.IsSymm]) (by simp [Matrix.IsSymm])
    (by simp [Matrix.IsSymm]) 0
    (fun _ => hexp 0)
    (fun _ => by simpa only [Pi.neg_def, neg_neg] using (hexp 0).neg)
    (fun _ => by simpa only [Pi.neg_def, neg_neg] using (hexp 0).neg)
    (by
      funext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct, Real.exp_zero]
      ring)
    (by
      funext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct, Real.exp_zero]
      ring)
  convert h using 1
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Real.exp_zero]
