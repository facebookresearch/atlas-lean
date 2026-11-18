/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Mechanics.PoroelasticEnergy

/-!
# Poroelastic port-energy checks

Focused checks for `PhyslibExt.Mechanics.PoroelasticEnergy`: a
one-coordinate trajectory with identity matrices, displacement
`u(τ) = τ`, constant pressure `1`, forcing `τ - 1` and source
`2` satisfies both balance equations, and the energy identity
applies at `t = 0`.

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix

/-- The identity at the concrete one-coordinate trajectory. -/
example : HasDerivAt
    (fun τ => (1 / 2) * (((fun _ => τ) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => τ) : Fin 1 → ℝ))
      + ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ))))
    (((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((fun _ => (0 : ℝ) - 1) : Fin 1 → ℝ)
      + ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((fun _ => (2 : ℝ)) : Fin 1 → ℝ)
      - ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ))) 0 :=
  Mechanics.Poroelastic.poroelastic_port_energy
    (K := 1) (Q := 1) (C := 1) (H := 1)
    (u := fun τ _ => τ) (p := fun _ _ => 1) (du := fun _ _ => 1)
    (dp := fun _ _ => 0) (f := fun τ _ => τ - 1) (s := fun _ _ => 2)
    (by simp [Matrix.IsSymm])
    (by simp [Matrix.IsSymm])
    (fun i t => hasDerivAt_id' t)
    (fun i t => hasDerivAt_const t 1)
    (fun t => by funext i; fin_cases i <;> simp <;> norm_num)
    (fun t => by funext i; fin_cases i <;> simp <;> norm_num)
    0
