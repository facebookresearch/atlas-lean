/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Macroeconomics.SectorBalances
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Macroeconomics.SectorBalances` -/

namespace MathlibExtTest.Economics.Macroeconomics.SectorBalances

open MathlibExt.Economics.Macroeconomics.SectorBalances

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

example : testAccounts.Y = testAccounts.C + testAccounts.I + testAccounts.G + testAccounts.NX :=
  expenditure_identity _ (by norm_num [testAccounts]) (by norm_num [testAccounts])

example : testAccounts.S = testAccounts.I + testAccounts.NX :=
  saving_investment_balance _ (by norm_num [testAccounts]) (by norm_num [testAccounts])
    (by norm_num [testAccounts]) (by norm_num [testAccounts]) (by norm_num [testAccounts])

end MathlibExtTest.Economics.Macroeconomics.SectorBalances
