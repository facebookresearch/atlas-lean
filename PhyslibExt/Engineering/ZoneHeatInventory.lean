/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import PhyslibExt.EarthScience.Compartments

/-!
# Zone-network heat inventory balance

## i. Overview

For a network of thermal zones with constant capacities and
reciprocal conductances, the derivative of the total heat inventory
is the total boundary input plus heating power: internal exchange
cancels by reciprocity.

## ii. Key results

- `ZoneHeatInventory.heat_inventory_hasDerivAt`: the inventory balance
  at one time, from the zone equations at that time.
- `ZoneHeatInventory.heat_inventory_deriv`: the inventory balance.

## iii. Table of contents

- A. Heat inventory

## iv. References

- Standard lumped-capacitance building thermal network models
  (RC-network formulation).

## A. Heat inventory
-/

@[expose] public section

namespace ZoneHeatInventory

/-- Zone heat inventory balance at one time `t`: with constant
capacities `C i`, reciprocal conductances `G i j = G j i`, zone
temperatures with derivatives `Tv i t` at `t`, and the zone equations
`C i * Tv i t = Σ j, G i j * (T j t - T i t) + b i t + P i t` at `t`,
the total heat inventory `Σ i, C i * T i` has derivative
`Σ i, (b i t + P i t)` at `t`: internal exchange cancels by
reciprocity. Only data at the single time `t` is assumed. -/
theorem heat_inventory_hasDerivAt {ι : Type*} [Fintype ι]
    (C : ι → ℝ) (G : ι → ι → ℝ) (T Tv b P : ι → ℝ → ℝ) (t : ℝ)
    (hG : ∀ i j, G i j = G j i)
    (hT : ∀ i, HasDerivAt (T i) (Tv i t) t)
    (hzone : ∀ i, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + b i t + P i t) :
    HasDerivAt (fun s => ∑ i, C i * T i s)
      (∑ i, (b i t + P i t)) t := by
  have hexch : ∀ i, (∑ j, G i j * (T j t - T i t))
      = ∑ j ∈ Finset.univ, (G j i * T j t - G i j * T i t) := by
    intro i
    apply Finset.sum_congr rfl
    intro j _
    rw [hG i j]
    ring
  have h := EarthScience.hasDerivAt_total_stock Finset.univ
    (fun i s => C i * T i s) (fun i j s => G i j * T i s)
    (fun i s => b i s + P i s) t (fun i _ => by
      show HasDerivAt (fun s => C i * T i s)
        ((∑ j ∈ Finset.univ, (G j i * T j t - G i j * T i t)) + (b i t + P i t)) t
      have hder : C i * Tv i t
          = (∑ j ∈ Finset.univ, (G j i * T j t - G i j * T i t)) + (b i t + P i t) := by
        rw [hzone i, hexch i, add_assoc]
      exact hder ▸ HasDerivAt.const_mul (C i) (hT i))
  exact h

/-- Zone heat inventory balance: for zones indexed by a fintype,
with constant capacities `C i`, reciprocal conductances
`G i j = G j i`, zone temperatures `T i t` with supplied derivatives
`Tv i t`, and zone equations
`C i * Tv i t = Σ j, G i j * (T j t - T i t) + b i t + P i t`,
the total heat inventory `Σ i, C i * T i t` has derivative
`Σ i, (b i t + P i t)`: internal exchange cancels by reciprocity. -/
theorem heat_inventory_deriv {ι : Type*} [Fintype ι]
    (C : ι → ℝ) (G : ι → ι → ℝ) (T Tv b P : ι → ℝ → ℝ)
    (hG : ∀ i j, G i j = G j i)
    (hT : ∀ i t, HasDerivAt (T i) (Tv i t) t)
    (hzone : ∀ i t, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + b i t + P i t)
    (t : ℝ) :
    HasDerivAt (fun s => ∑ i, C i * T i s)
      (∑ i, (b i t + P i t)) t :=
  heat_inventory_hasDerivAt C G T Tv b P t hG (fun i => hT i t) (fun i => hzone i t)

end ZoneHeatInventory
