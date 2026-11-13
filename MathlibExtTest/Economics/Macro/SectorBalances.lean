/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Macro.SectorBalances
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Macro.SectorBalances` -/

namespace MathlibExtTest.Economics.Macro.SectorBalances

open MathlibExt.Economics.Macro.SectorBalances

def testAccounts : SectorAccounts where
  Y := 100
  C := 50
  I := 10
  G := 20
  X := 30
  M := 10
  Sp := 25
  T := 25
  Sg := 5
  S := 30
  NX := 20
  gdp := by norm_num
  netExports := by norm_num
  incomeDisposal := by norm_num
  publicSaving := by norm_num
  nationalSaving := by norm_num

example : testAccounts.Y = testAccounts.C + testAccounts.I + testAccounts.G + testAccounts.NX :=
  expenditure_identity _

example : testAccounts.S = testAccounts.I + testAccounts.NX :=
  saving_investment_balance _

end MathlibExtTest.Economics.Macro.SectorBalances
