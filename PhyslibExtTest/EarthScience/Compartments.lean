/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Compartments

/-!
# Compartment conservation checks

Concrete consumers of `PhyslibExt.EarthScience.Compartments`: a numeric
two-compartment transfer matrix, the public shape of the derivative
theorems, and a closed two-compartment exchange whose total stock is
constant.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
exchange example has compartment `0` gaining at rate `1` and
compartment `1` losing at rate `1` through the single transfer
`1 → 0`; the closed-system theorem then gives derivative `0` for the
total, as it must since the two stocks are `t` and `-t`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Cancellation on a concrete transfer matrix
- B. Closed two-compartment exchange

## iv. References

- `PhyslibExt.EarthScience.Compartments`
-/

open Finset in
/-- Cancellation for the transfer rates `q i j = i + 2j` on `Fin 2`. -/
example : ∑ i : Fin 2, ∑ j : Fin 2,
    (((j : ℝ) + 2 * (i : ℝ)) - ((i : ℝ) + 2 * (j : ℝ))) = 0 :=
  EarthScience.sum_transfer_net_eq_zero Finset.univ
    (fun i j : Fin 2 => (i : ℝ) + 2 * (j : ℝ))

/-- The public statement shape of the open-system total derivative. -/
example {ι : Type*} (s : Finset ι) (m : ι → ℝ → ℝ) (q : ι → ι → ℝ → ℝ)
    (src : ι → ℝ → ℝ) (t : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (m i) (∑ j ∈ s, (q j i t - q i j t) + src i t) t) :
    HasDerivAt (fun t => ∑ i ∈ s, m i t) (∑ i ∈ s, src i t) t :=
  EarthScience.hasDerivAt_total_stock s m q src t h

/-- Closed two-compartment exchange at unit rate from `1` to `0`:
the total of the stocks `t` and `-t` has derivative `0`. -/
example (t : ℝ) :
    HasDerivAt
      (fun t => ∑ i : Fin 2, ![fun t => t, fun t => -t] i t) 0 t := by
  refine EarthScience.hasDerivAt_total_stock_eq_zero Finset.univ _
    (fun i j _ => if i = 1 ∧ j = 0 then 1 else 0) t ?_
  intro i _
  fin_cases i
  · have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
    exact h1.congr_deriv (by simp)
  · have h1 : HasDerivAt (fun t : ℝ => -t) (-1) t := (hasDerivAt_id' t).neg
    exact h1.congr_deriv (by simp)
