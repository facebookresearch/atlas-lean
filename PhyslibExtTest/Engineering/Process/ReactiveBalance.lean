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
case recovers the scaled concentration derivative. Concrete vessels apply
the mass-versus-volume results: constant density gives `V' = Qin - Qout`,
three changing-density vessels follow the comparison identity and break
that law, and one changing-density vessel keeps it because the two
corrections cancel.
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

-- Constant density rho = rho_in = 2 with Qin = 3 and Qout = 1: the vessel
-- V(t) = 2t satisfies the mass balance (2 * V)' = 2 * 3 - 2 * 1, so
-- `volume_balance_of_const_density` gives the volume law V' = Qin - Qout.
example : HasDerivAt (fun t : ℝ => 2 * t) (3 - 1) 0 := by
  have hV : HasDerivAt (fun t : ℝ => 2 * t) 2 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_mul 2).congr_deriv (mul_one 2)
  have hmass : HasDerivAt (fun t : ℝ => (2 : ℝ) * (2 * t)) (2 * 3 - 2 * 1) 0 :=
    (hV.const_mul 2).congr_deriv (by norm_num)
  exact hV.congr_deriv (volume_balance_of_const_density hV (by norm_num) 3 1 hmass)

-- Changing density can break the naive volume law: rho(t) = 1 + t and
-- V(t) = 1 - t keep the mass rho * V = 1 - t ^ 2 stationary at t = 0, so
-- the mass balance holds with Qin = Qout = 0 (inflow density 1). At
-- rho = 1, V = 1, rho' = 1, `volume_deriv_eq` gives
-- V' = rho_in / rho * Qin - Qout - V * rho' / rho = -1, and V' = Qin - Qout
-- is impossible.
example : HasDerivAt (fun t : ℝ => 1 - t) (1 / 1 * 0 - 0 - 1 * 1 / 1) 0 ∧
    ¬ HasDerivAt (fun t : ℝ => 1 - t) (0 - 0) 0 := by
  have hrho : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add 1
  have hV : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_sub 1
  have hmass : HasDerivAt (fun t : ℝ => (1 + t) * (1 - t))
      (1 * 0 - (1 + 0) * 0) 0 :=
    (hrho.mul hV).congr_deriv (by norm_num)
  refine ⟨hV.congr_deriv ((volume_deriv_eq hrho hV (by norm_num) 1 0 0 hmass).trans
    (by norm_num)), fun hnaive => ?_⟩
  have h := volume_deriv_eq hrho hnaive (by norm_num) 1 0 0 hmass
  norm_num at h

-- A second counterexample: rho(t) = 1 + t / 10 and V(t) = 10 - t
-- conserve mass at t = 0 with Qin = Qout = 1 (inflow density 1). At rho = 1,
-- V = 10, rho' = 1/10, `volume_deriv_eq` gives V' = -1, not Qin - Qout = 0.
example : HasDerivAt (fun t : ℝ => 10 - t) (1 / 1 * 1 - 1 - 10 * (1 / 10) / 1) 0 ∧
    ¬ HasDerivAt (fun t : ℝ => 10 - t) (1 - 1) 0 := by
  have hrho : HasDerivAt (fun t : ℝ => 1 + t / 10) (1 / 10) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).div_const 10).const_add 1
  have hV : HasDerivAt (fun t : ℝ => 10 - t) (-1) 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_sub 10
  have hmass : HasDerivAt (fun t : ℝ => (1 + t / 10) * (10 - t))
      (1 * 1 - (1 + 0 / 10) * 1) 0 :=
    (hrho.mul hV).congr_deriv (by norm_num)
  refine ⟨hV.congr_deriv ((volume_deriv_eq hrho hV (by norm_num) 1 1 1 hmass).trans
    (by norm_num)), fun hnaive => ?_⟩
  have h := volume_deriv_eq hrho hnaive (by norm_num) 1 1 1 hmass
  norm_num at h

-- Distinct values reach every term of the comparison identity: rho(t) = 2 + t,
-- inflow density 3, Qin = 4, Qout = 1 and V(t) = 5 + 5/2 t satisfy the mass
-- balance at t = 0, where rho = 2, V = 5, rho' = 1, so `volume_deriv_eq` gives
-- V' = 3 / 2 * 4 - 1 - 5 * 1 / 2 = 5/2, not Qin - Qout = 3.
example : HasDerivAt (fun t : ℝ => 5 + 5 / 2 * t) (3 / 2 * 4 - 1 - 5 * 1 / 2) 0 ∧
    ¬ HasDerivAt (fun t : ℝ => 5 + 5 / 2 * t) (4 - 1) 0 := by
  have hrho : HasDerivAt (fun t : ℝ => 2 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add 2
  have hV : HasDerivAt (fun t : ℝ => 5 + 5 / 2 * t) (5 / 2) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul (5 / 2)).congr_deriv (mul_one _)).const_add 5
  have hmass : HasDerivAt (fun t : ℝ => (2 + t) * (5 + 5 / 2 * t))
      (3 * 4 - (2 + 0) * 1) 0 :=
    (hrho.mul hV).congr_deriv (by norm_num)
  refine ⟨hV.congr_deriv ((volume_deriv_eq hrho hV (by norm_num) 3 4 1 hmass).trans
    (by norm_num)), fun hnaive => ?_⟩
  have h := volume_deriv_eq hrho hnaive (by norm_num) 3 4 1 hmass
  norm_num at h

-- The closure is sufficient, not necessary: rho(t) = 1 + t and V(t) = 1 + t
-- with inflow density 2, Qin = 1 and Qout = 0 satisfy the mass balance at
-- t = 0, where both sides are 2. There rho = 1, V = 1 and rho' = 1, so the two
-- corrections cancel, (rho_in - rho) * Qin = V * rho' = 1, and
-- `volume_deriv_eq` gives V' = 2 / 1 * 1 - 0 - 1 * 1 / 1 = Qin - Qout although
-- the density changes.
example : HasDerivAt (fun t : ℝ => 1 + t) (2 / 1 * 1 - 0 - 1 * 1 / 1) 0 ∧
    HasDerivAt (fun t : ℝ => 1 + t) (1 - 0) 0 := by
  have hrho : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add 1
  have hV : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add 1
  have hmass : HasDerivAt (fun t : ℝ => (1 + t) * (1 + t)) (2 * 1 - (1 + 0) * 0) 0 :=
    (hrho.mul hV).congr_deriv (by norm_num)
  have h := volume_deriv_eq hrho hV (by norm_num) 2 1 0 hmass
  exact ⟨hV.congr_deriv (h.trans (by norm_num)), hV.congr_deriv (h.trans (by norm_num))⟩

end Engineering.Process.ReactiveBalance.Tests
