/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Reactive balances: stock and concentration forms

## i. Overview

Variable-volume species balances at one instant. The amount (stock) of
species `i` is `n t i = V t * c t i` for liquid volume `V t` and
concentration `c t i`, in species molar units. With supplied derivatives,
the stock balance `n' = Fin - Fout + G` is equivalent to the concentration
form `V' * c i + V * c' i = Fin - Fout + G`; the `V' * c i` term is the
variable-volume contribution and does not vanish for constant
concentration. Division into concentration form needs nonzero volume at
the instant. Derivatives are hypotheses; no existence claim is made.

## ii. Key results

- `ReactiveBalance.stock_iff_concentration`: the stock and concentration
  balances are equivalent given the derivatives.
- `ReactiveBalance.concentration_deriv_eq_of_stock`: at nonzero volume the
  stock balance determines the concentration derivative.
- `ReactiveBalance.closed_constant_volume`: the closed constant-volume
  specialization `V0 * c' i = G`.
- `ReactiveBalance.volume_balance_of_const_density`: under the
  constant-density closure, the liquid mass balance gives the volume law
  `V' = Qin - Qout`; without that closure the comparison identity keeps
  the `-V * rho' / rho` term.

## iii. Table of contents

- A. Stock and concentration balances
- B. Mass versus volume balance

## iv. References

- R. M. Felder, R. W. Rousseau and L. G. Bullard, *Elementary Principles of
  Chemical Processes*, 4th ed., Wiley (2016), Chapter 4 (material balances
  on transient and reactive processes).
-/

@[expose] public section

namespace Engineering.Process.ReactiveBalance

/-! ## A. Stock and concentration balances -/

/-- Product rule for one species stock `V * c i`: its derivative is
`V' * c i + V * c' i` at the instant `t`. -/
theorem stock_deriv_eq {ι : Type*} {V : ℝ → ℝ} {c : ℝ → ι → ℝ}
    {V' : ℝ} {c' : ι → ℝ} {t : ℝ}
    (hV : HasDerivAt V V' t) (i : ι)
    (hc : HasDerivAt (fun t => c t i) (c' i) t) :
    HasDerivAt (fun t => V t * c t i) (V' * c t i + V t * c' i) t := by
  exact hV.fun_mul hc

/-- **Stock iff concentration balance.** With supplied derivatives, the
stock balance `n' = Fin - Fout + G` for species `i` holds exactly when the
concentration form `V' * c i + V * c' i = Fin - Fout + G` holds. The
`V' * c i` term is the variable-volume contribution; it does not vanish
just because the concentration is constant. -/
theorem stock_iff_concentration {ι : Type*} {V : ℝ → ℝ} {c : ℝ → ι → ℝ}
    {V' : ℝ} {c' : ι → ℝ} {t : ℝ}
    (hV : HasDerivAt V V' t) (i : ι)
    (hc : HasDerivAt (fun t => c t i) (c' i) t) (Fin Fout G : ℝ) :
    HasDerivAt (fun t => V t * c t i) (Fin - Fout + G) t ↔
      V' * c t i + V t * c' i = Fin - Fout + G := by
  have h := stock_deriv_eq hV i hc
  constructor
  · intro hstock
    exact h.unique hstock
  · intro heq
    rw [← heq]
    exact h

/-- At an instant of nonzero volume, the stock balance determines the
concentration derivative by division. At zero volume this division is not
available, which is why `V t ≠ 0` is a hypothesis. -/
theorem concentration_deriv_eq_of_stock {ι : Type*} {V : ℝ → ℝ}
    {c : ℝ → ι → ℝ} {V' : ℝ} {c' : ι → ℝ} {t : ℝ}
    (hV : HasDerivAt V V' t) (i : ι)
    (hc : HasDerivAt (fun t => c t i) (c' i) t)
    (hVt : V t ≠ 0) (Fin Fout G : ℝ)
    (hstock : HasDerivAt (fun t => V t * c t i) (Fin - Fout + G) t) :
    c' i = (Fin - Fout + G - V' * c t i) / V t := by
  have heq := (stock_iff_concentration hV i hc Fin Fout G).mp hstock
  rw [eq_div_iff hVt]
  linarith

/-- Closed constant-volume specialization: with the volume frozen at `V0`
and no inflow or outflow, the stock balance is `V0 * c' i = G`. -/
theorem closed_constant_volume {ι : Type*} {V0 : ℝ} {c : ℝ → ι → ℝ}
    {c' : ι → ℝ} {t : ℝ}
    (i : ι) (hc : HasDerivAt (fun t => c t i) (c' i) t) (G : ℝ) :
    HasDerivAt (fun t => V0 * c t i) G t ↔ V0 * c' i = G := by
  have h : HasDerivAt (fun t => V0 * c t i) (V0 * c' i) t := hc.const_mul V0
  constructor
  · intro hbal
    exact h.unique hbal
  · intro heq
    rw [← heq]
    exact h

/-! ## B. Mass versus volume balance -/

/-- General comparison identity: solving the mass balance for `V'` gives
`V' = (rho_in / rho) * Qin - Qout - V * rho' / rho`, which shows why mass
conservation alone is insufficient for a volume law when the density
changes. -/
theorem volume_deriv_eq {rho V : ℝ → ℝ} {rho' V' t : ℝ}
    (hrho : HasDerivAt rho rho' t) (hV : HasDerivAt V V' t)
    (hrho0 : rho t ≠ 0) (rho_in Qin Qout : ℝ)
    (hmass : HasDerivAt (fun t => rho t * V t)
      (rho_in * Qin - rho t * Qout) t) :
    V' = rho_in / rho t * Qin - Qout - V t * rho' / rho t := by
  have hmul := hrho.mul hV
  have heq := hmass.unique hmul
  field_simp
  linarith

/-- **Volume balance under the constant-density closure.** If
`rho = rho_in = rho0 > 0` is constant, the mass balance gives
`V' = Qin - Qout`. -/
theorem volume_balance_of_const_density {rho V : ℝ → ℝ} {V' t rho0 : ℝ}
    (hV : HasDerivAt V V' t) (hrho0 : 0 < rho0)
    (hrho : rho = fun _ => rho0) (Qin Qout : ℝ)
    (hmass : HasDerivAt (fun t => rho t * V t)
      (rho0 * Qin - rho0 * Qout) t) :
    V' = Qin - Qout := by
  have hrho0ne : rho0 ≠ 0 := ne_of_gt hrho0
  have hfun : (fun t => rho t * V t) = (fun t => rho0 * V t) := by
    funext x
    simp [hrho]
  have hmass' : HasDerivAt (fun t => rho0 * V t) (rho0 * Qin - rho0 * Qout) t :=
    hfun ▸ hmass
  have hmul := hV.const_mul rho0
  have heq := hmass'.unique hmul
  have h2 : rho0 * V' = rho0 * (Qin - Qout) := by linarith
  exact mul_left_cancel₀ hrho0ne h2

end Engineering.Process.ReactiveBalance
