/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Steady slab conduction: linear profile, zero second derivative, Fourier flux

## i. Overview

On a slab `[0, L]` with `L > 0`, constant conductivity and no heat
production, `T(z) = T0 + (TL - T0) * z / L` meets both boundary
temperatures, has constant derivative `(TL - T0) / L`, and second
derivative `0`; the Fourier heat flux is `q = -k * (TL - T0) / L`.
`z` is measured along the chosen axis, `k` in `W / (m K)`, `q` in `W / m ^ 2`.

## ii. Key results

- `EarthScience.slab_profile_boundary`: `T(0) = T0`, `T(L) = TL`.
- `EarthScience.hasDerivAt_slab_profile`: `T' = (TL - T0) / L`.
- `EarthScience.slab_profile_second_deriv`: `T'' = 0` and the flux formula.

## iii. Table of contents

- A. Boundary values and first derivative
- B. Second derivative and heat flux

## iv. References

- `HasDerivAt.const_mul` / `const_add` / `div_const` in Mathlib.
- `iteratedDeriv_succ` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- The linear slab profile meets both boundary temperatures. -/
theorem slab_profile_boundary {T0 TL L : ℝ} (hL : 0 < L) :
    (fun z => T0 + (TL - T0) * z / L) 0 = T0 ∧
      (fun z => T0 + (TL - T0) * z / L) L = TL := by
  constructor
  · simp
  · have hLne : L ≠ 0 := ne_of_gt hL
    field_simp
    ring

set_option linter.unusedVariables false in
/-- The slab profile has constant first derivative `(TL - T0) / L`. -/
theorem hasDerivAt_slab_profile {T0 TL L : ℝ} (hL : 0 < L) (z : ℝ) :
    HasDerivAt (fun z => T0 + (TL - T0) * z / L) ((TL - T0) / L) z := by
  have h := (((hasDerivAt_id' z).const_mul (TL - T0)).div_const L).const_add T0
  simpa using h

/-- The slab profile solves steady conduction: its second derivative is `0`,
and the Fourier heat flux is `q = -k * (TL - T0) / L`. -/
theorem slab_profile_second_deriv {T0 TL L k : ℝ} (hL : 0 < L) (z : ℝ) :
    iteratedDeriv 2 (fun z => T0 + (TL - T0) * z / L) z = 0 ∧
      -k * ((TL - T0) / L) = -k * (TL - T0) / L := by
  constructor
  · have hderiv : deriv (fun z => T0 + (TL - T0) * z / L) = fun _ => ((TL - T0) / L) :=
      funext (fun y => (hasDerivAt_slab_profile hL y).deriv)
    have h2 : (2 : ℕ) = 1 + 1 := rfl
    rw [h2, iteratedDeriv_succ, iteratedDeriv_one, hderiv]
    exact deriv_const _ _
  · ring

end EarthScience
