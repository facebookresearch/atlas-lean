/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.MultispeciesReactiveTransport

/-!
# Multispecies conservation checks

Consumers of `PhyslibExt.EarthScience.MultispeciesReactiveTransport`: the conservation
vector check `lᵀ S = 0` for the two-species reaction `A -> B`, and the
public shapes of both theorems.

## i. Overview

These are elaboration and non-vacuity checks, not new results. For
`A -> B` with `l = (1, 1)` and `S = (-1, 1)`, `lᵀ S = -1 + 1 = 0`, so the
reaction term drops out of the `l`-weighted balance.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Conservation vector for `A -> B`
- B. Shapes of the two theorems

## iv. References

- `PhyslibExt.EarthScience.MultispeciesReactiveTransport`
-/

/-- For `A -> B` with `l = (1, 1)`, `S = (-1, 1)`: `lᵀ S = 0`. -/
example : ∑ i : Fin 2, ![1, 1] i * (if i = 0 then (-1 : ℝ) else 1) = 0 := by
  rw [Fin.sum_univ_two]
  simp

/-- The public statement shape of the integrated multispecies balance. -/
example (n m : ℕ) (c J : ℝ → ℝ → Fin n → ℝ)
    (S : Fin n → Fin m → ℝ) (r : (Fin n → ℝ) → Fin m → ℝ)
    (l : Fin n → ℝ) (a b t : ℝ)
    (hpde : ∀ x i, deriv (fun t => c t x i) t + deriv (fun x => J t x i) x =
      ∑ j, S i j * r (c t x) j)
    (hcons : ∀ j, ∑ i, l i * S i j = 0)
    (ht_int : ∀ i, IntervalIntegrable (fun x => deriv (fun t => c t x i) t)
      MeasureTheory.volume a b)
    (hx_int : ∀ i, IntervalIntegrable (fun x => deriv (fun x => J t x i) x)
      MeasureTheory.volume a b)
    (hx_deriv : ∀ i x, HasDerivAt (fun x => J t x i) (deriv (fun x => J t x i) x) x)
    (hr_int : ∀ i, IntervalIntegrable (fun x => ∑ j, S i j * r (c t x) j)
      MeasureTheory.volume a b) :
    (∫ x in a..b, ∑ i, l i * deriv (fun t => c t x i) t) =
      -((∑ i, l i * J t b i) - ∑ i, l i * J t a i) :=
  EarthScience.multispecies_integrated n m c J S r l a b t hpde hcons ht_int
    hx_int hx_deriv hr_int

/-- The public statement shape of the multispecies mass-balance theorem. -/
example (n m : ℕ) (c J : ℝ → ℝ → Fin n → ℝ)
    (S : Fin n → Fin m → ℝ) (r : (Fin n → ℝ) → Fin m → ℝ)
    (l : Fin n → ℝ) (a b t : ℝ)
    (hpde : ∀ x i, deriv (fun t => c t x i) t + deriv (fun x => J t x i) x =
      ∑ j, S i j * r (c t x) j)
    (hcons : ∀ j, ∑ i, l i * S i j = 0)
    (ht_int : ∀ i, IntervalIntegrable (fun x => deriv (fun t => c t x i) t)
      MeasureTheory.volume a b)
    (hx_int : ∀ i, IntervalIntegrable (fun x => deriv (fun x => J t x i) x)
      MeasureTheory.volume a b)
    (hx_deriv : ∀ i x, HasDerivAt (fun x => J t x i) (deriv (fun x => J t x i) x) x)
    (hr_int : ∀ i, IntervalIntegrable (fun x => ∑ j, S i j * r (c t x) j)
      MeasureTheory.volume a b)
    (hswap : ∀ i, HasDerivAt (fun t => ∫ x in a..b, c t x i)
      (∫ x in a..b, deriv (fun t => c t x i) t) t)
    (hc_all : ∀ t' i, IntervalIntegrable (fun x => c t' x i)
      MeasureTheory.volume a b) :
    HasDerivAt (fun t => ∫ x in a..b, ∑ i, l i * c t x i)
      (-((∑ i, l i * J t b i) - ∑ i, l i * J t a i)) t :=
  EarthScience.multispecies_mass_balance n m c J S r l a b t hpde hcons ht_int
    hx_int hx_deriv hr_int hswap hc_all
