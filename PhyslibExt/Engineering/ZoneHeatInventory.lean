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

/-!
# Zone-network heat inventory balance

## i. Overview

For a network of thermal zones with constant capacities and
reciprocal conductances, the derivative of the total heat inventory
is the total boundary input plus heating power: internal exchange
cancels by reciprocity.

## ii. Key results

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
      (∑ i, (b i t + P i t)) t := by
  have hcancel : (∑ i, ∑ j, G i j * (T j t - T i t)) = 0 := by
    have hflip : (∑ i, ∑ j, G i j * (T j t - T i t))
        = ∑ i, ∑ j, G i j * (T i t - T j t) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
      rw [hG i j]
    have hneg : (∑ i, ∑ j, G i j * (T i t - T j t))
        = -(∑ i, ∑ j, G i j * (T j t - T i t)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    linarith
  have heq : (∑ i, C i * Tv i t) = ∑ i, (b i t + P i t) := by
    have hzone' : ∀ i, C i * Tv i t
        = (∑ j, G i j * (T j t - T i t)) + (b i t + P i t) := by
      intro i
      rw [hzone i t, add_assoc]
    calc (∑ i, C i * Tv i t)
        = ∑ i, ((∑ j, G i j * (T j t - T i t)) + (b i t + P i t)) :=
          Finset.sum_congr rfl (fun i _ => hzone' i)
      _ = (∑ i, ∑ j, G i j * (T j t - T i t)) + ∑ i, (b i t + P i t) :=
          Finset.sum_add_distrib
      _ = ∑ i, (b i t + P i t) := by rw [hcancel, zero_add]
  have hmain : HasDerivAt (fun s => ∑ i, C i * T i s) (∑ i, C i * Tv i t) t :=
    HasDerivAt.fun_sum (fun i _ => (hT i t).const_mul (C i))
  rw [heq] at hmain
  exact hmain

end ZoneHeatInventory
