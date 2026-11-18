/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Mechanics.VibroacousticEnergy

/-!
# Vibroacoustic port-energy checks

Focused checks for `PhyslibExt.Mechanics.VibroacousticEnergy`:
a one-coordinate system with identity mass and compliance,
zero stiffness, displacement `x(τ) = τ`, constant pressure
`1`, coupling `2`, damping `2`, and acoustic coefficient `-2`
satisfies both port equations, and the energy identity applies
at `t = 0` with both dissipation terms nonzero.

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix

/-- The identity at the concrete one-coordinate system. -/
example : HasDerivAt
    (fun τ => (1 / 2) * (((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ))
      + ((fun _ => τ) : Fin 1 → ℝ)
        ⬝ᵥ ((0 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => τ) : Fin 1 → ℝ))
      + ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ))))
    (-(((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ (((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ))
      + ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ (((-2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)))) 0 :=
  Mechanics.Vibroacoustic.vibroacoustic_port_energy
    (M := 1) (K := 0) (C := (2 : ℝ) • 1) (A := 1)
    (H := (-2 : ℝ) • 1) (G := (2 : ℝ) • 1)
    (x := fun τ _ => τ) (v := fun _ _ => 1) (dv := fun _ _ => 0)
    (p := fun _ _ => 1) (dp := fun _ _ => 0)
    (by simp [Matrix.IsSymm]) (by simp [Matrix.IsSymm])
    (by simp [Matrix.IsSymm])
    (fun i t => hasDerivAt_id' t)
    (fun i t => hasDerivAt_const t 1)
    (fun i t => hasDerivAt_const t 1)
    (fun t => by funext i; fin_cases i <;> simp <;> norm_num)
    (fun t => by funext i; fin_cases i <;> simp <;> rw [Matrix.neg_mulVec] <;> simp)
    0
