/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (distinct labels, squares) of the identification Root8[12]+ <->
Twelfth[34]- (record r8f:R86+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The odd labels of the target representation are pairwise distinct. -/
theorem wR8fR86p_odist : labDistinct wR8fR86pW.sh.odd 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The sum of the squares of the odd terms of the target representation. -/
theorem wR8fR86p_osq : sqSumZ wR8fR86pW.sh.odd = 512000 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
