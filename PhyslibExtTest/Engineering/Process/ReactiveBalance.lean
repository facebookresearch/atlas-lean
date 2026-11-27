/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.ReactiveBalance

import Mathlib.Tactic.NormNum

/-!
# Tests for reactive balances

Boundary checks for `PhyslibExt.Engineering.Process.ReactiveBalance`:
growing volume at constant concentration still grows the stock, zero
volume blocks the concentration division, and the closed constant-volume
case recovers the scaled concentration derivative.
-/

namespace Engineering.Process.ReactiveBalance.Tests

open Engineering.Process.ReactiveBalance

-- The product-rule API itself: V(t) = 1 + t and one species with
-- supplied concentration derivative `c' 0`. The stock derivative is
-- `1 * 2 + (1 + 0) * c' 0` by `stock_deriv_eq`.
example {c' : Fin 1 → ℝ}
    (hc : HasDerivAt (fun t : ℝ => (fun _ _ => (2 : ℝ)) t (0 : Fin 1))
      (c' 0) 0) :
    HasDerivAt (fun t : ℝ => (1 + t) * ((fun _ _ => (2 : ℝ)) t (0 : Fin 1)))
      (1 * 2 + (1 + 0) * c' 0) 0 := by
  have hV : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add 1
  exact stock_deriv_eq (V := fun t : ℝ => 1 + t) (c := fun _ _ => (2 : ℝ))
    (V' := (1 : ℝ)) (t := (0 : ℝ)) hV (0 : Fin 1) hc

-- The equivalence API itself at the same fed-batch instant, with flows
-- Fin - Fout + G = 3 - 1 + 0.
example :
    (HasDerivAt (fun t : ℝ => (1 + t) * ((fun _ _ => (2 : ℝ)) t (0 : Fin 1)))
      (3 - 1 + 0) 0) ↔ (1 : ℝ) * 2 + (1 + 0) * 0 = 3 - 1 + 0 := by
  have hV : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add 1
  have hc0 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 0 := hasDerivAt_const 0 2
  exact stock_iff_concentration (V := fun t : ℝ => 1 + t) (c := fun _ _ => (2 : ℝ))
    (V' := (1 : ℝ)) (c' := fun _ : Fin 1 => (0 : ℝ)) (t := (0 : ℝ))
    hV (0 : Fin 1) hc0 3 1 0

-- The division API itself at the same fed-batch instant: for any
-- supplied concentration derivative `c' 0` compatible with the constant
-- concentration and with the stock balance `3 - 1 + 0`, division by the
-- nonzero volume gives `c' 0 = (3 - 1 + 0 - 1 * 2) / (1 + 0)`. This is an
-- application of `concentration_deriv_eq_of_stock`, not arithmetic alone.
example {c' : Fin 1 → ℝ}
    (hc : HasDerivAt (fun t : ℝ => (fun _ _ => (2 : ℝ)) t (0 : Fin 1))
      (c' 0) 0)
    (hstock : HasDerivAt
      (fun t : ℝ => (1 + t) * ((fun _ _ => (2 : ℝ)) t (0 : Fin 1)))
      (3 - 1 + 0) 0) :
    c' 0 = (3 - 1 + 0 - 1 * 2) / (1 + 0) := by
  have hV : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add 1
  have hVt : (1 : ℝ) + 0 ≠ 0 := by norm_num
  exact concentration_deriv_eq_of_stock (V := fun t : ℝ => 1 + t)
    (c := fun _ _ => (2 : ℝ)) (V' := (1 : ℝ)) (t := (0 : ℝ))
    hV (0 : Fin 1) hc hVt 3 1 0 hstock

-- The closed constant-volume API itself: V0 = 2 and c(t) = 3t.
example :
    (HasDerivAt (fun t : ℝ => 2 * ((fun t _ => 3 * t) t (0 : Fin 1))) 6 1) ↔
      (2 : ℝ) * 3 = 6 := by
  have hc : HasDerivAt (fun t : ℝ => 3 * t) 3 1 := by
    have h := HasDerivAt.const_mul (3 : ℝ) (hasDerivAt_id' (1 : ℝ))
    rw [mul_one] at h
    exact h
  exact closed_constant_volume (V0 := (2 : ℝ)) (c := fun t _ => 3 * t)
    (c' := fun _ : Fin 1 => (3 : ℝ)) (t := (1 : ℝ)) (0 : Fin 1) hc 6

-- Zero volume at the instant: the division hypothesis `V t ≠ 0` fails,
-- while the stock derivative is still 2 through the product rule.
example : HasDerivAt (fun t : ℝ => t * 2) 2 0 ∧ ¬ ((0 : ℝ) ≠ 0) := by
  constructor
  · have h := HasDerivAt.mul_const (hasDerivAt_id' (0 : ℝ)) (2 : ℝ)
    rw [one_mul] at h
    exact h
  · simp

end Engineering.Process.ReactiveBalance.Tests
