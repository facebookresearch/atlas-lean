/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import MathlibExt.RingTheory.MvPowerSeries.AdicComplete

open MvPowerSeries

/-- Multivariate power series over the `p`-adic integers are adically
complete at the maximal ideal. -/
example (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℤ_[p]))
      (MvPowerSeries (Fin 2) ℤ_[p]) :=
  MvPowerSeries.isAdicComplete_maximalIdeal
