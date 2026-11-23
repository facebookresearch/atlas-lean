/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Finite compartment models: internal transfers cancel

The total stock of a finite compartment (box) model changes only through
external sources: every internal transfer is one compartment's outflow and
another's inflow, so the transfers cancel in the derivative of the total.

## i. Overview

Fix a finite set `s` of compartments. The stock in compartment `i` at time
`t` is `m i t`, the transfer rate from compartment `i` to compartment `j`
is `q i j t`, and the external source rate into compartment `i` is
`src i t`. The compartment balance for one stock reads
`m i' t = ∑ j ∈ s, (q j i t - q i j t) + src i t`: inflows minus outflows,
plus what enters from outside the system.

This file proves the two facts every later box model in this development
uses: the net internal transfer summed over all compartments is zero
(`sum_transfer_net_eq_zero`), and therefore the derivative of the total
stock `∑ i ∈ s, m i t` is the sum of the external sources
(`hasDerivAt_total_stock`), which is `0` for a closed system
(`hasDerivAt_total_stock_eq_zero`). The transfer law is a hypothesis of
the model, not a derived physical law, and no positivity or sign
assumptions on stocks, transfers, or sources are made.

## ii. Key results

- `EarthScience.sum_transfer_net_eq_zero`: the summed net transfer is `0`.
- `EarthScience.hasDerivAt_total_stock`: the total stock's derivative is
  the sum of the external source rates.
- `EarthScience.hasDerivAt_total_stock_eq_zero`: a closed system
  conserves its total stock to first order.

## iii. Table of contents

- A. Cancellation of internal transfers
- B. Derivative of the total stock

## iv. References

- `HasDerivAt.fun_sum` in `Mathlib/Analysis/Calculus/Deriv/Add.lean`
  (Mathlib), which sums derivatives over a `Finset`.

## A. Cancellation of internal transfers
-/

@[expose] public section

namespace EarthScience

/-- Net internal transfer over a finite compartment system is zero:
every transfer `q i j` out of compartment `i` into compartment `j` is
counted once with each sign. -/
theorem sum_transfer_net_eq_zero {ι : Type*} (s : Finset ι) (q : ι → ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (q j i - q i j) = 0 := by
  simp only [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr Finset.sum_comm

/-! ## B. Derivative of the total stock -/

/-- If every stock `m i` obeys the compartment balance
`m i' t = ∑ j, (q j i t - q i j t) + src i t` at time `t`, where
`q i j t` is the transfer rate from compartment `i` to compartment `j`
and `src i t` is the external source rate into compartment `i`, then
the total stock `∑ i, m i` has derivative `∑ i, src i t` at `t`:
internal transfers cancel and only external sources change the total. -/
theorem hasDerivAt_total_stock {ι : Type*} (s : Finset ι)
    (m : ι → ℝ → ℝ) (q : ι → ι → ℝ → ℝ) (src : ι → ℝ → ℝ) (t : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (m i) (∑ j ∈ s, (q j i t - q i j t) + src i t) t) :
    HasDerivAt (fun t => ∑ i ∈ s, m i t) (∑ i ∈ s, src i t) t := by
  have hsum : HasDerivAt (fun t => ∑ i ∈ s, m i t)
      (∑ i ∈ s, ((∑ j ∈ s, (q j i t - q i j t)) + src i t)) t :=
    HasDerivAt.fun_sum h
  have hz : (∑ i ∈ s, ∑ j ∈ s, (q j i t - q i j t)) = 0 :=
    sum_transfer_net_eq_zero s (fun i j => q i j t)
  have hval : (∑ i ∈ s, ((∑ j ∈ s, (q j i t - q i j t)) + src i t))
      = ∑ i ∈ s, src i t := by
    rw [Finset.sum_add_distrib, hz, zero_add]
  rwa [hval] at hsum

/-- Closed compartment systems conserve total stock to first order:
with no external sources, the total stock has derivative `0`. -/
theorem hasDerivAt_total_stock_eq_zero {ι : Type*} (s : Finset ι)
    (m : ι → ℝ → ℝ) (q : ι → ι → ℝ → ℝ) (t : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (m i) (∑ j ∈ s, (q j i t - q i j t)) t) :
    HasDerivAt (fun t => ∑ i ∈ s, m i t) 0 t := by
  have hsum : HasDerivAt (fun t => ∑ i ∈ s, m i t)
      (∑ i ∈ s, (∑ j ∈ s, (q j i t - q i j t))) t :=
    HasDerivAt.fun_sum h
  have hz : (∑ i ∈ s, ∑ j ∈ s, (q j i t - q i j t)) = 0 :=
    sum_transfer_net_eq_zero s (fun i j => q i j t)
  rwa [hz] at hsum

end EarthScience
