/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Compartments

/-!
# Finite flowsheets: whole-network species balance

## i. Overview

A finite process flowsheet over process units and species. For each
species, every unit obeys a holdup balance whose internal transfer from
unit `i` to unit `j` appears once as an outflow of `i` and once as an
inflow of `j`; external inflow, external outflow, and generation are
supplied separately. Summing the unit balances, every internal transfer
cancels and the total holdup of each species changes only through the
external terms and generation. This is one instantiation of the finite
compartment result `EarthScience.hasDerivAt_total_stock`, imported here.
The unit balances are hypotheses of the model; no dynamics existence is
claimed. This `Flowsheet` structure is the single graph type reused by
later network models.

## ii. Key results

- `Flowsheet.species_balance`: the whole-network species balance.
- `Flowsheet.species_balance_closed`: zero net supplied rate in every unit
  gives zero total-holdup derivative at the instant.

## iii. Table of contents

- A. The flowsheet structure and its species balance

## iv. References

- R. M. Felder, R. W. Rousseau and L. G. Bullard, *Elementary Principles of
  Chemical Processes*, 4th ed., Wiley (2016), Chapter 4 (multiple-unit
  material balances).
- `PhyslibExt/EarthScience/Compartments.lean`:
  `EarthScience.hasDerivAt_total_stock`, imported here.
-/

@[expose] public section

namespace Engineering.Process.Flowsheets

/-- A finite process flowsheet over process units and species. For each
species, every unit obeys a holdup balance whose internal transfer from
unit `i` to unit `j` appears once as an outflow of `i` and once as an
inflow of `j`; external inflow, external outflow, and generation are
supplied separately. This is the single graph type reused by later network
models; dynamics existence is not claimed, since the unit balances are
hypotheses. -/
structure Flowsheet (Unit Species : Type*) [Fintype Unit] where
  /-- Holdup (amount stock) of each species in each unit over time. -/
  holdup : Species → Unit → ℝ → ℝ
  /-- Internal transfer rate of a species from the first unit to the second. -/
  transfer : Species → Unit → Unit → ℝ → ℝ
  /-- External inflow rate of each species into each unit. -/
  externalIn : Species → Unit → ℝ → ℝ
  /-- External outflow rate of each species from each unit. -/
  externalOut : Species → Unit → ℝ → ℝ
  /-- Supplied generation rate of each species in each unit. -/
  generation : Species → Unit → ℝ → ℝ
  /-- Each unit balance: internal inflows minus internal outflows, plus
  external inflow minus external outflow plus generation. -/
  balance : ∀ (s : Species) (u : Unit) (t : ℝ),
    HasDerivAt (holdup s u)
      ((∑ j : Unit, (transfer s j u t - transfer s u j t)) +
        (externalIn s u t - externalOut s u t + generation s u t)) t

namespace Flowsheet

/-- **Whole-network species balance.** For each species, the derivative of
the total holdup over all units is the summed external inflow minus
external outflow plus generation; every internal transfer cancels. This is
one instantiation of `EarthScience.hasDerivAt_total_stock`. -/
theorem species_balance {Unit Species : Type*} [Fintype Unit]
    (F : Flowsheet Unit Species) (s : Species) (t : ℝ) :
    HasDerivAt (fun t => ∑ u : Unit, F.holdup s u t)
      (∑ u : Unit,
        (F.externalIn s u t - F.externalOut s u t + F.generation s u t)) t := by
  have h := EarthScience.hasDerivAt_total_stock (Finset.univ : Finset Unit)
    (fun u t' => F.holdup s u t')
    (fun i j t' => F.transfer s i j t')
    (fun u t' => F.externalIn s u t' - F.externalOut s u t' + F.generation s u t')
    t
    (fun u _ => F.balance s u t)
  simpa using h

/-- Closed case at an instant: if the net supplied rate of the species is
zero in every unit at `t`, the total holdup has derivative zero at `t`. -/
theorem species_balance_closed {Unit Species : Type*} [Fintype Unit]
    (F : Flowsheet Unit Species) (s : Species) (t : ℝ)
    (h : ∀ u : Unit,
      F.externalIn s u t - F.externalOut s u t + F.generation s u t = 0) :
    HasDerivAt (fun t => ∑ u : Unit, F.holdup s u t) 0 t := by
  have hb := species_balance F s t
  have h0 : (∑ u : Unit, (F.externalIn s u t - F.externalOut s u t + F.generation s u t)) = 0 :=
    Finset.sum_eq_zero (fun u _ => h u)
  rwa [h0] at hb

end Flowsheet

end Engineering.Process.Flowsheets
