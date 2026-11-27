/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Demand, supply and partial equilibrium

Demand and supply schedules `D S : ℝ → ℝ` give quantities as functions of price. Excess demand
is `D p - S p`, and `p` is an equilibrium (market-clearing) price when `D p = S p`.

This is the market interface for the Atlas EC08 targets.

## Main definitions

* `MathlibExt.Economics.Market.excessDemand`
* `MathlibExt.Economics.Market.IsEquilibrium`
-/

@[expose] public section

namespace MathlibExt.Economics.Market

/-- Excess demand `D p - S p` at price `p`. -/
def excessDemand (D S : ℝ → ℝ) (p : ℝ) : ℝ :=
  D p - S p

/-- `p` is a market-clearing (equilibrium) price: quantity demanded equals quantity
supplied. -/
def IsEquilibrium (D S : ℝ → ℝ) (p : ℝ) : Prop :=
  D p = S p

end MathlibExt.Economics.Market
