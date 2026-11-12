/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.K03CarbonCycle

/-!
# Carbon-cycle checks

Concrete consumers of `PhyslibExt.EarthScience.K03CarbonCycle`:
the public shapes of the three theorems, a concrete
atmosphere / ocean / land flux set, and the closed-system boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
fluxes `Fao = 1, Foa = 2, Fal = 3, Fla = 4, Fol = 5, Flo = 6` and
externals `0.1, 0.2, 0.3`, the reservoir derivatives are `2.1, 0.2, -1.7`
and the total is `0.6`, the sum of the externals.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Finite-reservoir shapes
- B. Atmosphere / ocean / land numeric case and closed boundary

## iv. References

- `PhyslibExt.EarthScience.K03CarbonCycle`
-/

/-- Public shape of the finite-reservoir theorem. -/
example {ι : Type*} (s : Finset ι) {C : ι → ℝ → ℝ} {F : ι → ι → ℝ → ℝ}
    {e : ι → ℝ → ℝ} {t : ℝ}
    (h : ∀ i ∈ s, HasDerivAt (C i)
      ((∑ j ∈ s, (F j i t - F i j t)) + e i t) t) :
    HasDerivAt (fun t => ∑ i ∈ s, C i t) (∑ i ∈ s, e i t) t :=
  EarthScience.carbon_total_deriv s h

/-- Public shape of the closed finite-reservoir theorem. -/
example {ι : Type*} (s : Finset ι) {C : ι → ℝ → ℝ} {F : ι → ι → ℝ → ℝ} {t : ℝ}
    (h : ∀ i ∈ s, HasDerivAt (C i) (∑ j ∈ s, (F j i t - F i j t)) t) :
    HasDerivAt (fun t => ∑ i ∈ s, C i t) 0 t :=
  EarthScience.carbon_total_deriv_closed s h

/-- Public shape of the atmosphere / ocean / land specialization. -/
example {Catm Cocean Cland : ℝ → ℝ} {t : ℝ}
    {Fao Foa Fal Fla Fol Flo e_atm e_ocean e_land : ℝ}
    (hatm : HasDerivAt Catm ((Foa - Fao) + (Fla - Fal) + e_atm) t)
    (hocean : HasDerivAt Cocean ((Fao - Foa) + (Flo - Fol) + e_ocean) t)
    (hland : HasDerivAt Cland ((Fal - Fla) + (Fol - Flo) + e_land) t) :
    HasDerivAt (fun t => Catm t + Cocean t + Cland t)
      (e_atm + e_ocean + e_land) t :=
  EarthScience.carbon_atmosphere_ocean_land hatm hocean hland

/-- Numeric atmosphere / ocean / land cancellation. -/
example : ((2 - 1) + (4 - 3) + 0.1) + (((1 - 2) + (6 - 5) + 0.2) +
    ((3 - 4) + (5 - 6) + 0.3)) = (0.1 + 0.2 + 0.3 : ℝ) := by
  norm_num

/-- Closed atmosphere / ocean / land: total derivative is `0` with zero externals. -/
example {Catm Cocean Cland : ℝ → ℝ} {t : ℝ} {Fao Foa Fal Fla Fol Flo : ℝ}
    (hatm : HasDerivAt Catm ((Foa - Fao) + (Fla - Fal) + 0) t)
    (hocean : HasDerivAt Cocean ((Fao - Foa) + (Flo - Fol) + 0) t)
    (hland : HasDerivAt Cland ((Fal - Fla) + (Fol - Flo) + 0) t) :
    HasDerivAt (fun t => Catm t + Cocean t + Cland t) 0 t := by
  have h := EarthScience.carbon_atmosphere_ocean_land hatm hocean hland
  simpa using h
