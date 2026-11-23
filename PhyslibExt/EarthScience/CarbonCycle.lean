/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.Ring

/-!
# Carbon cycle and chemical coupling

For finite carbon reservoirs with transfer fluxes `F_ij`, the total
carbon derivative is the sum of the external fluxes: internal transfers
cancel in pairs. For a closed system the total derivative is `0`. The
atmosphere / ocean / land specialization makes the cancellation
explicit with named pairwise fluxes. Carbon is in moles or mass of
carbon; carbonate speciation and alkalinity are separate state
constraints, not formalized here.

## i. Overview

Summing the reservoir balances cancels every internal flux twice
(once with each sign), leaving only external fluxes. The three-reservoir
specialization is the same cancellation with explicit flux names.

## ii. Key results

- `EarthScience.carbon_total_deriv`: total carbon derivative is the sum of external fluxes.
- `EarthScience.carbon_total_deriv_closed`: closed total carbon derivative is `0`.
- `EarthScience.carbon_atmosphere_ocean_land`: atmosphere / ocean / land specialization.

## iii. Table of contents

- A. Finite-reservoir cancellation
- B. Atmosphere / ocean / land

## iv. References

- `HasDerivAt.fun_sum` / `HasDerivAt.add` in Mathlib.
- `Finset.sum_comm` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Internal pairwise fluxes cancel when summed over all reservoirs. -/
private theorem internal_flux_cancel {ι : Type*} (s : Finset ι)
    (F : ι → ι → ℝ → ℝ) (t : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (F j i t - F i j t)) = 0 := by
  simp only [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr Finset.sum_comm

/-- Finite carbon reservoirs: if each reservoir `i` obeys
`C_i' = sum_j (F_{j i} - F_{i j}) + e_i` (internal transfers cancel in
pairs, `e_i` external), then the total carbon derivative is the sum of
the external fluxes. -/
theorem carbon_total_deriv {ι : Type*} (s : Finset ι)
    {C : ι → ℝ → ℝ} {F : ι → ι → ℝ → ℝ} {e : ι → ℝ → ℝ} {t : ℝ}
    (h : ∀ i ∈ s, HasDerivAt (C i)
      ((∑ j ∈ s, (F j i t - F i j t)) + e i t) t) :
    HasDerivAt (fun t => ∑ i ∈ s, C i t) (∑ i ∈ s, e i t) t := by
  have hsum := HasDerivAt.fun_sum h
  have hcancel : (∑ i ∈ s, ((∑ j ∈ s, (F j i t - F i j t)) + e i t))
      = ∑ i ∈ s, e i t := by
    rw [Finset.sum_add_distrib, internal_flux_cancel s F t, zero_add]
  rw [hcancel] at hsum
  exact hsum

/-- Closed finite carbon system: with no external fluxes the total carbon
has derivative `0`. -/
theorem carbon_total_deriv_closed {ι : Type*} (s : Finset ι)
    {C : ι → ℝ → ℝ} {F : ι → ι → ℝ → ℝ} {t : ℝ}
    (h : ∀ i ∈ s, HasDerivAt (C i) (∑ j ∈ s, (F j i t - F i j t)) t) :
    HasDerivAt (fun t => ∑ i ∈ s, C i t) 0 t := by
  have hsum := HasDerivAt.fun_sum h
  rw [internal_flux_cancel s F t] at hsum
  exact hsum

/-- Atmosphere / ocean / land specialization: with pairwise transfers
`Fao` (atmosphere to ocean), `Foa`, `Fal`, `Fla`, `Fol`, `Flo` and
external fluxes `e_atm, e_ocean, e_land`, the total carbon derivative is
`e_atm + e_ocean + e_land`; internal transfers cancel. -/
theorem carbon_atmosphere_ocean_land {Catm Cocean Cland : ℝ → ℝ} {t : ℝ}
    {Fao Foa Fal Fla Fol Flo e_atm e_ocean e_land : ℝ}
    (hatm : HasDerivAt Catm ((Foa - Fao) + (Fla - Fal) + e_atm) t)
    (hocean : HasDerivAt Cocean ((Fao - Foa) + (Flo - Fol) + e_ocean) t)
    (hland : HasDerivAt Cland ((Fal - Fla) + (Fol - Flo) + e_land) t) :
    HasDerivAt (fun t => Catm t + Cocean t + Cland t)
      (e_atm + e_ocean + e_land) t := by
  have h123 := (hatm.add hocean).add hland
  convert h123 using 1
  ring

end EarthScience
