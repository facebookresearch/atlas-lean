/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Steady vapor diffusion through layers in series

## i. Overview

Layers in series with vapor resistances `R i` between fixed
boundary partial pressures `pin` and `pout` carry the common
steady vapor mass flux `(pin - pout) / ∑ i, R i`. The interface
pressure after the first `m` layers is `pin` minus the flux times
the prefix resistance; vapor mass flux and partial pressure keep
their own dimensions and no heat-flux formula is asserted.

## ii. Key results

- `Engineering.VaporSeries.vaporInterfacePressure_zero`: the
  zeroth interface is the
  inner boundary pressure.
- `Engineering.VaporSeries.vaporInterfacePressure_last`: the
  final interface is the
  outer boundary pressure when the total resistance is nonzero.
- `Engineering.VaporSeries.vaporInterfacePressure_succ_sub`:
  adjacent interfaces differ
  by the common flux times the intervening resistance.

## iii. Table of contents

- A. Series flux and interface pressures

## iv. References

- Standard steady-state (Glaser) vapor diffusion through a
  multilayer wall assembly.
-/

@[expose] public section

/-! ## A. Series flux and interface pressures -/
namespace Engineering.VaporSeries


/-- Steady vapor mass flux through layers in series from boundary
partial pressures `pin` and `pout` and layer vapor resistances
`R i`: the total pressure drop divided by the total resistance.
This is the totalized quotient: it is the physical steady flux
only when the total resistance is nonzero (in particular for
positive resistances); at zero total resistance Lean's division
gives `0`, which has no physical steady-state meaning. Vapor
mass flux and partial pressure keep their own dimensions; no
heat-flux formula is asserted. -/
noncomputable def vaporSeriesFlux {n : ℕ} (R : ℕ → ℝ)
    (pin pout : ℝ) : ℝ :=
  (pin - pout) / (∑ i ∈ Finset.range n, R i)

/-- Interface vapor pressure after the first `m` layers, using the
common series flux and the prefix resistance. The modeled
interfaces are `m ≤ n`; for `m > n` this formula continues the
prefix sum formally and is not a modeled interface. -/
noncomputable def vaporInterfacePressure {n : ℕ} (R : ℕ → ℝ)
    (pin pout : ℝ) (m : ℕ) : ℝ :=
  pin - vaporSeriesFlux (n := n) R pin pout
    * (∑ i ∈ Finset.range m, R i)

/-- The zeroth interface is the inner boundary pressure. -/
theorem vaporInterfacePressure_zero {n : ℕ} (R : ℕ → ℝ)
    (pin pout : ℝ) :
    vaporInterfacePressure (n := n) R pin pout 0 = pin := by
  simp [vaporInterfacePressure]

/-- The final interface is the outer boundary pressure when the
total series resistance is nonzero. -/
theorem vaporInterfacePressure_last {n : ℕ} (R : ℕ → ℝ)
    (pin pout : ℝ) (hR : (∑ i ∈ Finset.range n, R i) ≠ 0) :
    vaporInterfacePressure (n := n) R pin pout n = pout := by
  unfold vaporInterfacePressure vaporSeriesFlux
  rw [div_mul_cancel₀ _ hR]
  exact sub_sub_self _ _

/-- Adjacent interface pressures within the modeled layers
(`m < n`) differ by the common flux times the intervening layer
resistance. -/
theorem vaporInterfacePressure_succ_sub {n m : ℕ} (R : ℕ → ℝ)
    (pin pout : ℝ) (_hm : m < n) :
    vaporInterfacePressure (n := n) R pin pout m
        - vaporInterfacePressure (n := n) R pin pout (m + 1)
      = vaporSeriesFlux (n := n) R pin pout * R m := by
  unfold vaporInterfacePressure
  rw [Finset.sum_range_succ, mul_add, ← sub_sub]
  exact sub_sub_self _ _

/-- Validity of the flux quotient: when the total resistance is
nonzero, the series flux times the total resistance recovers
the boundary pressure drop. -/
theorem vaporSeriesFlux_mul_total {n : ℕ} (R : ℕ → ℝ)
    (pin pout : ℝ) (hR : (∑ i ∈ Finset.range n, R i) ≠ 0) :
    vaporSeriesFlux (n := n) R pin pout
        * (∑ i ∈ Finset.range n, R i) = pin - pout := by
  unfold vaporSeriesFlux
  exact div_mul_cancel₀ _ hR

end Engineering.VaporSeries
