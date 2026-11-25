/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.ScottContinuity.ContinuousLattice
public import Mathlib.Tactic

open MathlibExt.Order.ScottContinuity.ContinuousLattice

/-- The two-element lattice is continuous, so the hypothesis of the wanted inverse-limit theorem
is satisfiable by a lattice with two distinct elements. -/
example : IsContinuousLattice Bool := isContinuousLattice_bool

/-- In `Bool`, `true` is way below itself (it is a compact element). -/
example : WayBelow true true := by
  have h := isContinuousLattice_bool true
  by_contra hn
  have : sSup {x : Bool | WayBelow x true} ≤ false := sSup_le fun x hx => by
    cases x
    · exact le_rfl
    · exact absurd hx hn
  rw [← h] at this
  exact absurd this (by decide)
