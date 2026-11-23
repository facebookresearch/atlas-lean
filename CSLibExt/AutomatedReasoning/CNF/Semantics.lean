/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics

/-! Compatibility aliases for the pre-rename `Cslib.CookLevin` names. -/

@[expose] public section

namespace Cslib.CookLevin

export Cslib.Logic.PL (CNFClause CNF CNFSat cnfSat_iff_exists_satisfies)

namespace CNFLiteral

export Cslib.Logic.PL.CNFLiteral (Satisfies satisfies_def)

end CNFLiteral

namespace CNFClause

export Cslib.Logic.PL.CNFClause (Satisfies satisfies_def satisfies_nil
  satisfies_cons)

end CNFClause

namespace CNF

export Cslib.Logic.PL.CNF (Satisfies satisfies_def satisfies_nil
  satisfies_cons)

end CNF

end Cslib.CookLevin
