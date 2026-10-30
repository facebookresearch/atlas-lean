/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Compatibility tests: the legacy AutomatedReasoning module paths must keep
exposing the pre-rename `Cslib.CookLevin` CNF/DPLL API.
-/
module

public import CSLibExt.AutomatedReasoning.DPLL.Solver
public import CSLibExt.AutomatedReasoning.DPLL.Correctness

@[expose] public section

#check Cslib.CookLevin.CNF.restrict
#check Cslib.CookLevin.CNF.satisfies_congr
#check Cslib.CookLevin.CNF.satisfies_of_satisfies_restrict
#check Cslib.CookLevin.CNF.sat_iff_restrict_true_or_false
#check Cslib.CookLevin.CNF.sat_iff_restrict_of_unit
#check Cslib.CookLevin.CNFSat
#check Cslib.CookLevin.DPLL.firstUnit
#check Cslib.CookLevin.DPLL.decideWithFuel
#check Cslib.CookLevin.DPLL.dpll_eq_true_iff
