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
rectangular client with two displacement coordinates and one
pressure coordinate. With identity storage and dissipation,
the all-ones rectangular coupling, displacement `τ` in both
coordinates, constant pressure `1`, forcing `τ - 1`, and source
`3`, both balance equations hold and the energy identity
applies at `t = 0`.

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix

/-- Rectangular client: two displacement coordinates and one
pressure coordinate. -/
example : HasDerivAt
    (fun τ => (1 / 2) * (((fun _ => τ) : Fin 2 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)
          *ᵥ ((fun _ => τ) : Fin 2 → ℝ))
      + ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ))))
    (((fun _ => (1 : ℝ)) : Fin 2 → ℝ)
        ⬝ᵥ ((fun _ => (0 : ℝ) - 1) : Fin 2 → ℝ)
      + ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((fun _ => (3 : ℝ)) : Fin 1 → ℝ)
      - ((fun _ => (1 : ℝ)) : Fin 1 → ℝ)
        ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          *ᵥ ((fun _ => (1 : ℝ)) : Fin 1 → ℝ))) 0 :=
  Mechanics.Poroelastic.poroelastic_port_energy
    (K := 1) (Q := fun _ _ => 1) (C := 1) (H := 1)
    (u := fun τ _ => τ) (p := fun _ _ => 1) (du := fun _ _ => 1)
    (dp := fun _ _ => 0) (f := fun τ _ => τ - 1) (s := fun _ _ => 3)
    (by simp [Matrix.IsSymm])
    (by simp [Matrix.IsSymm])
    (fun i t => hasDerivAt_id' t)
    (fun i t => hasDerivAt_const t 1)
    (fun t => by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct])
    (fun t => by
      funext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct, Matrix.transpose]
      norm_num)
    0
