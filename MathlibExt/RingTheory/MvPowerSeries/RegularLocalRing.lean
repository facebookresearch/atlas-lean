/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsRegularLocalRing_mvPowerSeries_fin.lean` and
`P2M/Sol/S_IsRegularLocalRing_mvPowerSeries_fin.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style. The multivariable power
series isomorphisms in the source are replaced by the corresponding
Mathlib equivalences, which subsume them.
-/

module

public import MathlibExt.RingTheory.PowerSeries.RegularLocalRing
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Multivariable power series over a regular local ring are regular local

By induction on the number of variables, using the identification of
`MvPowerSeries (Fin (n + 1)) 𝓞` with power series over
`MvPowerSeries (Fin n) 𝓞` and the fact that power series over a regular
local ring are regular local.
-/

@[expose] public section

/-- Multivariable power series over a regular local ring form a
regular local ring. The discrete-valuation-ring case follows by typeclass
inference, since a DVR is a regular local ring. -/
theorem IsRegularLocalRing.mvPowerSeries_fin (𝓞 : Type*) [CommRing 𝓞]
    [IsRegularLocalRing 𝓞] (n : ℕ) : IsRegularLocalRing (MvPowerSeries (Fin n) 𝓞) := by
  induction n with
  | zero =>
    exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) 𝓞).toRingEquiv.symm
  | succ n ih =>
    haveI := ih
    haveI : IsRegularLocalRing (PowerSeries (MvPowerSeries (Fin n) 𝓞)) :=
      PowerSeries.isRegularLocalRing_powerSeries _
    exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.finSuccEquiv 𝓞 n).toRingEquiv.symm
