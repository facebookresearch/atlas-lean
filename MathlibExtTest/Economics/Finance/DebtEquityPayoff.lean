/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DebtEquityPayoff
public import MathlibExt.Probability.Finance.OptionPayoffs
import Mathlib.Tactic.NormNum

/-!
# Tests for debt and equity payoffs

Solvent (`V = 120, F = 100`), default (`V = 60, F = 100`), and at-the-money
(`V = F = 100`) firms: debt and call (equity) payoffs and their sum.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.DebtEquityPayoff

open _root_.MathlibExt.Economics.Finance.DebtEquityPayoff
open _root_.MathlibExt.Probability.Finance.OptionPayoffs



-- Solvent: V = 120, F = 100.
example : debtPayoff 120 100 = 100 := by
  unfold debtPayoff
  norm_num

example : europeanCallPayoff 120 100 = 20 := by
  unfold europeanCallPayoff
  norm_num

example : debtPayoff 120 100 + europeanCallPayoff 120 100 = 120 :=
  debtPayoff_add_europeanCallPayoff 120 100

-- Default: V = 60, F = 100.
example : debtPayoff 60 100 = 60 := by
  unfold debtPayoff
  norm_num

example : europeanCallPayoff 60 100 = 0 := by
  unfold europeanCallPayoff
  norm_num

example : debtPayoff 60 100 + europeanCallPayoff 60 100 = 60 :=
  debtPayoff_add_europeanCallPayoff 60 100

-- At-the-money: V = F = 100.
example : debtPayoff 100 100 = 100 := by
  unfold debtPayoff
  norm_num

example : europeanCallPayoff 100 100 = 0 := by
  unfold europeanCallPayoff
  norm_num

example : debtPayoff 100 100 + europeanCallPayoff 100 100 = 100 :=
  debtPayoff_add_europeanCallPayoff 100 100


end MathlibExtTest.Economics.Finance.DebtEquityPayoff
