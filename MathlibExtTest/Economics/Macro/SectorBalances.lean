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

/-- Private consumption `C = 50`, gross capital formation `I = 10` (private and government),
government consumption `G = 20`, net exports `NX = 20`, net taxes `T = 25`: GDP `Y = 100`,
private saving `25`, government saving `5`, national saving `30`. -/
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

example : testAccounts.S = testAccounts.I + testAccounts.NX :=
  saving_investment_balance _

/-- The derived balance pins `I + NX` to the recorded national saving `30`. -/
example : testAccounts.I + testAccounts.NX = 30 := by
  rw [← saving_investment_balance]
  rfl

end MathlibExtTest.Economics.Macro.SectorBalances
