/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Thermodynamics.RenewableEnergyPorts

/-!
# Solar-thermal receiver checks

Concrete consumers of
`PhyslibExt.Thermodynamics.RenewableEnergyPorts`: a numeric receiver
with `Ta = 300`, `G = 1000`, `α = 1`, `U = 0`, `K = 1`, whose
stagnation temperature solves `T^4 - 300^4 = 1000`, and the endpoint
values of the ideal objective.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric receiver stagnation and endpoints

## iv. References

- `PhyslibExt.Thermodynamics.RenewableEnergyPorts`
-/

/-- Existence and uniqueness of the numeric stagnation temperature,
with the defining balance. -/
example : ∃! Tstag : ℝ, (300 : ℝ) < Tstag ∧
    RenewableEnergyPorts.receiverLoss 0 1 300 Tstag = 1 * 1000 :=
  RenewableEnergyPorts.receiver_stagnationTemperature (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At ambient the loss is zero and the ideal objective vanishes at
both endpoints for any stagnation temperature. -/
example (Tstag : ℝ) (hT : Tstag ≠ 0)
    (hstag : RenewableEnergyPorts.receiverLoss 0 1 300 Tstag = 1 * 1000) :
    RenewableEnergyPorts.receiverLoss 0 1 300 300 = 0 ∧
      RenewableEnergyPorts.receiverObjective 1 1000 0 1 300 Tstag = 0 :=
  ⟨RenewableEnergyPorts.receiverLoss_ambient 0 1 300,
   (RenewableEnergyPorts.receiver_objective_endpoints (by norm_num)
     (by norm_num) hT hstag).2⟩

/-- Concrete definition check: the stagnation balance for these
parameters is the expanded polynomial equation
`Tstag^4 - 300^4 = 1000`, read directly off `receiverLoss`. -/
example (Tstag : ℝ)
    (hstag : RenewableEnergyPorts.receiverLoss 0 1 300 Tstag = 1 * 1000) :
    Tstag ^ 4 - 300 ^ 4 = 1000 := by
  simpa [RenewableEnergyPorts.receiverLoss] using hstag

/-- Concrete efficiency evaluation at ambient: at `T = Ta = 300`
the loss vanishes, so `receiverEfficiency 1 1000 0 1 300 300`
is `(1000 - 0) / 1000 = 1`, read directly off the definition. -/
example : RenewableEnergyPorts.receiverEfficiency 1 1000 0 1 300 300 = 1 := by
  simp [RenewableEnergyPorts.receiverEfficiency,
    RenewableEnergyPorts.receiverLoss]
