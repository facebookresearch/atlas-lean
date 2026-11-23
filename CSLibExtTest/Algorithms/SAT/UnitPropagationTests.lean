/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.UnitPropagation.Basic

@[expose] public section

/-!
# Tests for unit-propagation conflicts

Conflict derivations over the canonical `Cslib.Logic.PL.CNF` representation, and the
soundness theorems applied to them.
-/

open Cslib.Logic.PL
open Cslib.Algorithms.SAT.UnitPropagation

/-- Boundary check: a unit clause and its negation derive a unit-propagation conflict. -/
example : UPConflict [[(0, true)], [(0, false)]] :=
  UPConflict.step _ (0, true) (by decide) (UPConflict.empty _ (by decide))

/-- Boundary check: a formula containing the empty clause derives a conflict immediately. -/
example : UPConflict [[]] :=
  UPConflict.empty _ (by decide)

/-- Soundness applied: no assignment satisfies a unit clause together with its negation. -/
example : ¬∃ assignment, CNF.Satisfies assignment [[(0, true)], [(0, false)]] :=
  upConflict_unsat (UPConflict.step _ (0, true) (by decide) (UPConflict.empty _ (by decide)))
