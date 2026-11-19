/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.FixedCarrierTransport
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fixed-carrier transport checks

Concrete consumers of
`PhyslibExt.EarthScience.FixedCarrierTransport` on a
balanced two-cell carrier flow (`Q = 2` from cell `0` to
cell `1`, external inflow `2` at cell `0`, outflow `2` at
cell `1`, capacities `10`, concentrations `(3, 0)`): the
zero timestep, step values and stored-mass round trip,
physical sorption capacities, and necessity controls for
the balance, capacity, timestep, flow sign, and budget
hypotheses.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Balanced two-cell step
- B. Necessity controls

## iv. References

- `PhyslibExt.EarthScience.FixedCarrierTransport`
-/

open Matrix
open MathlibExt.Combinatorics.Graph.ArcNetwork
open EarthScience.FixedCarrierTransport

namespace PhyslibExtTest.EarthScience.FixedCarrierTransport

/-! ## A. Balanced two-cell step -/

/-- The two-cell carrier flow is balanced. -/
private lemma balanced_two :
    IsCarrierBalanced (![0] : Fin 1 → Fin 2) ![1] ![2] ![2, 0] ![0, 2] := by
  intro i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, incidenceMatrix, Fin.sum_univ_one]

/-- Zero timestep: the step is the identity. -/
example (i : Fin 2) :
    concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] 0 ![2] ![2, 0]
      ![0, 0] ![0, 0] ![3, 0] i = ![3, 0] i := by
  simp [concentrationStep]

/-- Step values at `dt = 1`: `(2.4, 0.6)`, and stored mass
`(24, 6)` with total `30` conserved. -/
example : concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] 1 ![2]
      ![2, 0] ![0, 0] ![0, 0] ![3, 0] 0 = 12 / 5 ∧
    concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] 1 ![2]
      ![2, 0] ![0, 0] ![0, 0] ![3, 0] 1 = 3 / 5 ∧
    (fun i => ![10, 10] i * concentrationStep (![0] : Fin 1 → Fin 2) ![1]
      ![10, 10] 1 ![2] ![2, 0] ![0, 0] ![0, 0] ![3, 0] i) = ![24, 6] := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]
  · norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]
  · funext i
    fin_cases i <;>
      norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]

/-- Unequal capacities `(10, 20)`: the receiving step is
`0.3`. -/
example : concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 20] 1 ![2]
    ![2, 0] ![0, 0] ![0, 0] ![3, 0] 1 = 3 / 10 := by
  norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]

/-- Physical sorption capacities (volume `5`, porosity
`1`, bulk density and distribution coefficient `1`, so
capacity `10`): stored mass and concentration after the
step are nonnegative, by the physical headline theorem. -/
example : ∀ i, 0 ≤ EarthScience.storedMass 5 1 1 1
      (concentrationStep (![0] : Fin 1 → Fin 2) ![1]
        (fun _j => EarthScience.storedMassCoefficient 5 1 1 1) 1 ![2] ![2, 0]
        ![0, 0] ![0, 0] ![3, 0] i) ∧
    0 ≤ concentrationStep (![0] : Fin 1 → Fin 2) ![1]
      (fun _j => EarthScience.storedMassCoefficient 5 1 1 1) 1 ![2] ![2, 0]
      ![0, 0] ![0, 0] ![3, 0] i := by
  apply storedMass_concentrationStep_nonneg (![0] : Fin 1 → Fin 2) ![1]
    (vol := fun _ => 5) (phi := fun _ => 1) (rho_b := fun _ => 1)
    (Kd := fun _ => 1) (dt := 1) (Q := ![2]) (qin := ![2, 0])
    (cin := ![0, 0]) (qout := ![0, 2]) (k := ![0, 0]) (c := ![3, 0])
  · intro i
    norm_num
  · intro i
    norm_num
  · intro i
    norm_num
  · intro i
    norm_num
  · norm_num
  · intro e
    fin_cases e
    norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · exact balanced_two
  · intro i
    fin_cases i <;>
      norm_num [Finset.sum_filter, Fin.sum_univ_one,
        EarthScience.storedMassCoefficient]

/-- On a balanced ring the step is the periodic upwind
update `(1 - ν) c₀ + ν c₁` with `ν = dt Q / C = 1 / 5`:
`2.6` at cell `0`. -/
example : concentrationStep (![0, 1] : Fin 2 → Fin 2) ![1, 0] ![10, 10] 1
      ![2, 2] ![0, 0] ![0, 0] ![0, 0] ![3, 1] 0
    = (1 - 1 / 5) * 3 + (1 / 5) * 1 := by
  norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_two]

/-! ## B. Necessity controls -/

/-- One-way flow without balancing external flow is not
balanced, and the inventory identity fails at cell `0`
(mass read of the step is `30`, inventory update reads
`24`). -/
example : ¬ IsCarrierBalanced (![0] : Fin 1 → Fin 2) ![1] ![2] ![0, 0]
    ![0, 0] ∧
    (![10, 10] 0 * concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] 1
      ![2] ![0, 0] ![0, 0] ![0, 0] ![3, 0] 0) ≠
    (((fun i => ![10, 10] i * ![3, 0] i)
      + incidenceMatrix (![0] : Fin 1 → Fin 2) ![1]
        *ᵥ (fun e => 1 * ![2] e * ![3, 0] ((![0] : Fin 1 → Fin 2) e))
      + (fun i => 1 * ![0, 0] i * ![0, 0] i)
      - (fun i => 1 * (![0, 0] i / ![10, 10] i + ![0, 0] i)
        * (![10, 10] i * ![3, 0] i))) : Fin 2 → ℝ) 0 := by
  constructor
  · intro hbal
    have h0 := hbal 0
    simp [Matrix.mulVec, dotProduct, incidenceMatrix] at h0
  · norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one,
      Matrix.mulVec, dotProduct, incidenceMatrix, Pi.add_apply, Pi.sub_apply]

/-- Balance is needed for nonnegativity: a large clean
unbalanced inflow dilutes cell `0` below zero in the
mixing form. -/
example : concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] 1 ![2]
    ![100, 0] ![0, 0] ![0, 0] ![3, 0] 0 = -27 := by
  norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]

/-- Zero capacity is totalized junk: the step reads the
old concentration while the stored mass reads zero, so
the nonzero-capacity hypothesis cannot be dropped. -/
example : concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![0, 10] 1 ![2]
    ![2, 0] ![0, 0] ![0, 0] ![3, 0] 0 = 3 ∧
    ![0, 10] 0 * concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![0, 10] 1 ![2]
      ![2, 0] ![0, 0] ![0, 0] ![3, 0] 0 = 0 ∧
    ¬ ∀ i, (![0, 10] : Fin 2 → ℝ) i ≠ 0 := by
  refine ⟨?_, by norm_num, fun h => h 0 (by norm_num)⟩
  norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]

/-- Negative timestep drives the receiving concentration
negative on the balanced flow. -/
example : concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] (-1) ![2]
    ![2, 0] ![0, 0] ![0, 0] ![3, 0] 1 = -3 / 5 := by
  norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]

/-- Negative carrier flow (balanced by reversed external
flows) drives the receiving concentration negative. -/
example : IsCarrierBalanced (![0] : Fin 1 → Fin 2) ![1] ![-2] ![0, 2]
    ![2, 0] ∧
    concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] 1 ![-2]
      ![0, 2] ![0, 0] ![0, 0] ![3, 0] 1 = -3 / 5 := by
  constructor
  · intro i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, incidenceMatrix]
  · norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]

/-- Excess outgoing step: at `dt = 10` the budget fails at
cell `0` (`2 ≤ 1` is false) and the step goes negative. -/
example : concentrationStep (![0] : Fin 1 → Fin 2) ![1] ![10, 10] 10 ![2]
    ![2, 0] ![0, 0] ![0, 0] ![3, 0] 0 = -3 := by
  norm_num [concentrationStep, Finset.sum_filter, Fin.sum_univ_one]

#print axioms
  EarthScience.FixedCarrierTransport.concentrationStep_inventory
#print axioms
  EarthScience.FixedCarrierTransport.concentrationStep_total
#print axioms
  EarthScience.FixedCarrierTransport.concentrationStep_nonneg
#print axioms
  EarthScience.FixedCarrierTransport.storedMass_concentrationStep_nonneg

end PhyslibExtTest.EarthScience.FixedCarrierTransport
