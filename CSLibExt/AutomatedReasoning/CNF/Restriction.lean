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
public import CSLibExt.Logics.Propositional.CNF.Restriction

/-! Compatibility aliases for the pre-rename `Cslib.CookLevin` names. -/

@[expose] public section

namespace Cslib.CookLevin

export Cslib.Logic.PL (CNFClause CNF CNFSat cnfSat_iff_exists_satisfies)

namespace CNFLiteral

export Cslib.Logic.PL.CNFLiteral (Satisfies satisfies_def)

end CNFLiteral

namespace CNFClause

export Cslib.Logic.PL.CNFClause (Satisfies satisfies_def satisfies_nil
  satisfies_cons vars mem_vars restrict mem_restrict vars_restrict_subset
  fst_not_mem_vars_restrict satisfies_restrict_iff)

end CNFClause

namespace CNF

export Cslib.Logic.PL.CNF (Satisfies satisfies_def satisfies_nil
  satisfies_cons vars vars_nil vars_cons mem_vars restrict restrict_nil
  restrict_cons vars_restrict_subset not_mem_vars_restrict
  vars_restrict_ssubset card_vars_restrict_lt satisfies_restrict_iff
  satisfies_congr satisfies_of_satisfies_restrict
  sat_iff_restrict_true_or_false sat_iff_restrict_of_unit)

end CNF

end Cslib.CookLevin
