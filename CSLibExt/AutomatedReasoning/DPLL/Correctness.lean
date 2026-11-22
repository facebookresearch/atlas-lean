/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.CookLevin
public import CSLibExt.Algorithms.SAT.DPLL.Correctness
public import CSLibExt.AutomatedReasoning.DPLL.Solver

/-! Compatibility aliases for the pre-rename `Cslib.CookLevin.DPLL` names. -/

@[expose] public section

namespace Cslib.CookLevin.DPLL

export Cslib.Algorithms.SAT.DPLL (firstUnit firstVariable clauseSatisfied
  formulaSatisfied clauseSatisfied_eq_true_iff formulaSatisfied_eq_true_iff
  decideWithFuel dpll firstUnit_eq_some_mem firstVariable_eq_some_mem_vars
  firstVariable_eq_none_all_empty any_isEmpty_eq_true_iff
  not_sat_of_mem_empty decideWithFuel_eq_true_iff dpll_eq_true_iff)

end Cslib.CookLevin.DPLL
